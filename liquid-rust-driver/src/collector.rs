use std::{collections::HashMap, path::PathBuf};

use itertools::Itertools;
use liquid_rust_common::{
    config::{self, AssertBehavior, CrateConfig},
    iter::IterExt,
};
use liquid_rust_syntax::{
    parse_fn_surface_sig, parse_qualifier, parse_refined_by, parse_ty,
    surface::{self},
    ParseErrorKind, ParseResult,
};
use rustc_ast::{
    tokenstream::TokenStream, AttrItem, AttrKind, Attribute, MacArgs, MetaItemKind, NestedMetaItem,
};
use rustc_errors::ErrorReported;
use rustc_hash::FxHashMap;
use rustc_hir::{
    def_id::LocalDefId, itemlikevisit::ItemLikeVisitor, ForeignItem, ImplItem, ImplItemKind, Item,
    ItemKind, TraitItem, VariantData,
};
use rustc_middle::ty::TyCtxt;
use rustc_session::{Session, SessionDiagnostic};
use rustc_span::Span;

pub(crate) struct SpecCollector<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    specs: Specs,
    sess: &'a Session,
    error_reported: bool,
}

pub(crate) struct Specs {
    pub fns: FxHashMap<LocalDefId, FnSpec>,
    pub structs: FxHashMap<LocalDefId, surface::StructDef>,
    pub enums: FxHashMap<LocalDefId, surface::EnumDef>,
    pub qualifs: Vec<surface::Qualifier>,
    pub crate_config: Option<config::CrateConfig>,
}

pub(crate) struct FnSpec {
    pub fn_sig: Option<surface::FnSig>,
    pub assume: bool,
}

impl<'tcx, 'a> SpecCollector<'tcx, 'a> {
    pub(crate) fn collect(tcx: TyCtxt<'tcx>, sess: &'a Session) -> Result<Specs, ErrorReported> {
        let mut collector = Self { tcx, sess, specs: Specs::new(), error_reported: false };

        tcx.hir().visit_all_item_likes(&mut collector);

        collector.parse_crate_spec(tcx.hir().krate_attrs())?;

        if collector.error_reported {
            Err(ErrorReported)
        } else {
            Ok(collector.specs)
        }
    }

    fn parse_fn_spec(
        &mut self,
        def_id: LocalDefId,
        attrs: &[Attribute],
    ) -> Result<(), ErrorReported> {
        let mut attrs = self.parse_liquid_attrs(attrs)?;
        self.report_dups(&attrs)?;
        // TODO(nilehmann) error if it has non-fun attrs

        let assume = attrs.assume();
        let fn_sig = attrs.fn_sig();

        self.specs.fns.insert(def_id, FnSpec { fn_sig, assume });
        Ok(())
    }

    fn parse_enum_def(
        &mut self,
        def_id: LocalDefId,
        attrs: &[Attribute],
    ) -> Result<(), ErrorReported> {
        let mut attrs = self.parse_liquid_attrs(attrs)?;
        self.report_dups(&attrs)?;
        let opaque = attrs.opaque();
        let refined_by = attrs.refined_by();
        self.specs
            .enums
            .insert(def_id, surface::EnumDef { refined_by, opaque });
        Ok(())
    }

    fn parse_struct_def(
        &mut self,
        def_id: LocalDefId,
        attrs: &[Attribute],
        data: &VariantData,
    ) -> Result<(), ErrorReported> {
        let mut attrs = self.parse_liquid_attrs(attrs)?;
        self.report_dups(&attrs)?;
        // TODO(nilehmann) error on field attrs if opaque
        // TODO(nilehmann) error if it has non-struct attrs

        let opaque = attrs.opaque();

        let refined_by = attrs.refined_by();

        let fields = data
            .fields()
            .iter()
            .map(|field| self.parse_field_spec(self.tcx.hir().attrs(field.hir_id)))
            .try_collect_exhaust()?;

        self.specs
            .structs
            .insert(def_id, surface::StructDef { refined_by, fields, opaque });

        Ok(())
    }

    fn parse_crate_spec(&mut self, attrs: &[Attribute]) -> Result<(), ErrorReported> {
        // TODO(atgeller) error if non-crate attributes
        // TODO(atgeller) error if >1 cfg attributes

        let mut attrs = self.parse_liquid_attrs(attrs)?;
        let mut qualifiers = attrs.qualifiers();
        self.specs.qualifs.append(&mut qualifiers);

        let crate_config = attrs.crate_config();
        self.specs.crate_config = crate_config;
        Ok(())
    }

    fn parse_field_spec(
        &mut self,
        attrs: &[Attribute],
    ) -> Result<Option<surface::Ty>, ErrorReported> {
        let mut attrs = self.parse_liquid_attrs(attrs)?;
        self.report_dups(&attrs)?;
        Ok(attrs.field())
    }

    fn parse_liquid_attrs(&mut self, attrs: &[Attribute]) -> Result<LiquidAttrs, ErrorReported> {
        let attrs: Vec<_> = attrs
            .iter()
            .filter_map(|attr| {
                if let AttrKind::Normal(attr_item, ..) = &attr.kind {
                    match &attr_item.path.segments[..] {
                        [first, ..] if first.ident.as_str() == "lr" => Some(attr_item),
                        _ => None,
                    }
                } else {
                    None
                }
            })
            .map(|attr_item| self.parse_liquid_attr(attr_item))
            .try_collect_exhaust()?;

        Ok(LiquidAttrs::new(attrs))
    }

    fn parse_liquid_attr(&mut self, attr_item: &AttrItem) -> Result<LiquidAttr, ErrorReported> {
        let segment = match &attr_item.path.segments[..] {
            [_, segment] => segment,
            _ => return self.emit_err(errors::InvalidAttr { span: attr_item.span() }),
        };

        let kind = match (segment.ident.as_str(), &attr_item.args) {
            ("sig", MacArgs::Delimited(span, _, tokens)) => {
                let fn_sig = self.parse(tokens.clone(), span.entire(), parse_fn_surface_sig)?;
                // print!("LR::SIG {:#?} \n", fn_sig);
                LiquidAttrKind::FnSig(fn_sig)
            }
            ("qualifier", MacArgs::Delimited(span, _, tokens)) => {
                let qualifer = self.parse(tokens.clone(), span.entire(), parse_qualifier)?;
                LiquidAttrKind::Qualifier(qualifer)
            }
            ("cfg", MacArgs::Delimited(_, _, _)) => {
                match LiquidAttrCFG::parse_cfg(attr_item) {
                    Err(error) => return self.emit_err(error),
                    Ok(mut cfg) => {
                        match cfg.try_into_crate_cfg() {
                            Err(error) => return self.emit_err(error),
                            Ok(crate_cfg) => LiquidAttrKind::CrateConfig(crate_cfg),
                        }
                    }
                }
            }
            ("refined_by", MacArgs::Delimited(span, _, tokens)) => {
                let refined_by = self.parse(tokens.clone(), span.entire(), parse_refined_by)?;
                LiquidAttrKind::RefinedBy(refined_by)
            }
            ("field", MacArgs::Delimited(span, _, tokens)) => {
                let ty = self.parse(tokens.clone(), span.entire(), parse_ty)?;
                LiquidAttrKind::Field(ty)
            }
            ("opaque", MacArgs::Empty) => LiquidAttrKind::Opaque,
            ("assume", MacArgs::Empty) => LiquidAttrKind::Assume,
            _ => return self.emit_err(errors::InvalidAttr { span: attr_item.span() }),
        };
        Ok(LiquidAttr { kind, span: attr_item.span() })
    }

    fn parse<T>(
        &mut self,
        tokens: TokenStream,
        input_span: Span,
        parser: impl FnOnce(TokenStream, Span) -> ParseResult<T>,
    ) -> Result<T, ErrorReported> {
        match parser(tokens, input_span) {
            Ok(result) => Ok(result),
            Err(err) => {
                let msg = match err.kind {
                    ParseErrorKind::UnexpectedEOF => "type annotation ended unexpectedly",
                    ParseErrorKind::UnexpectedToken => "unexpected token",
                    ParseErrorKind::IntTooLarge => "integer literal is too large",
                };

                self.emit_err(errors::SyntaxErr { span: err.span, msg })
            }
        }
    }

    fn report_dups(&mut self, attrs: &LiquidAttrs) -> Result<(), ErrorReported> {
        let mut has_dups = false;
        for (name, dups) in attrs.dups() {
            has_dups = true;
            for attr in dups {
                self.sess
                    .emit_err(errors::DuplicatedAttr { span: attr.span, name });
            }
        }
        if has_dups {
            self.error_reported = true;
            Err(ErrorReported)
        } else {
            Ok(())
        }
    }

    fn emit_err<T>(&mut self, err: impl SessionDiagnostic<'a>) -> Result<T, ErrorReported> {
        self.error_reported = true;
        self.sess.emit_err(err);
        Err(ErrorReported)
    }
}

impl<'hir> ItemLikeVisitor<'hir> for SpecCollector<'_, '_> {
    fn visit_item(&mut self, item: &'hir Item<'hir>) {
        match &item.kind {
            ItemKind::Fn(..) => {
                let hir_id = item.hir_id();
                let attrs = self.tcx.hir().attrs(hir_id);
                let _ = self.parse_fn_spec(item.def_id, attrs);
            }
            ItemKind::Struct(data, ..) => {
                let hir_id = item.hir_id();
                let attrs = self.tcx.hir().attrs(hir_id);
                let _ = self.parse_struct_def(item.def_id, attrs, data);
            }
            ItemKind::Enum(..) => {
                let hir_id = item.hir_id();
                let attrs = self.tcx.hir().attrs(hir_id);
                let _ = self.parse_enum_def(item.def_id, attrs);
            }
            ItemKind::Mod(..) => {
                // TODO: Parse mod level attributes
            }
            _ => (),
        }
    }

    fn visit_trait_item(&mut self, _trait_item: &'hir TraitItem<'hir>) {}
    fn visit_impl_item(&mut self, item: &'hir ImplItem<'hir>) {
        if let ImplItemKind::Fn(..) = &item.kind {
            let hir_id = item.hir_id();
            let attrs = self.tcx.hir().attrs(hir_id);
            let _ = self.parse_fn_spec(item.def_id, attrs);
        }
    }
    fn visit_foreign_item(&mut self, _foreign_item: &'hir ForeignItem<'hir>) {}
}

impl Specs {
    fn new() -> Specs {
        Specs {
            fns: FxHashMap::default(),
            structs: FxHashMap::default(),
            enums: FxHashMap::default(),
            qualifs: Vec::default(),
            crate_config: None,
        }
    }
}

#[derive(Debug)]
struct LiquidAttrs {
    map: HashMap<&'static str, Vec<LiquidAttr>>,
}

#[derive(Debug)]
struct LiquidAttr {
    kind: LiquidAttrKind,
    span: Span,
}

#[derive(Debug)]
enum LiquidAttrKind {
    Assume,
    Opaque,
    FnSig(surface::FnSig),
    RefinedBy(surface::Params),
    Qualifier(surface::Qualifier),
    Field(surface::Ty),
    CrateConfig(config::CrateConfig),
}

macro_rules! read_attr {
    ($self:expr, $name:literal, $kind:ident) => {
        $self
            .map
            .remove($name)
            .unwrap_or_else(|| vec![])
            .into_iter()
            .find_map(
                |attr| if let LiquidAttrKind::$kind(sig) = attr.kind { Some(sig) } else { None },
            )
    };
}

// like read_attr, but returns all valid attributes
macro_rules! read_all_attrs {
    ($self:expr, $name:literal, $kind:ident) => {
        $self
            .map
            .remove($name)
            .unwrap_or_else(|| vec![])
            .into_iter()
            .filter_map(
                |attr| if let LiquidAttrKind::$kind(sig) = attr.kind { Some(sig) } else { None },
            )
            .collect()
    };
}

impl LiquidAttrs {
    fn new(attrs: Vec<LiquidAttr>) -> Self {
        LiquidAttrs { map: attrs.into_iter().into_group_map_by(|attr| attr.kind.name()) }
    }

    fn dups(&self) -> impl Iterator<Item = (&'static str, &[LiquidAttr])> {
        self.map
            .iter()
            .filter(|(_, attrs)| attrs.len() > 1)
            .map(|(name, attrs)| (*name, &attrs[1..]))
    }

    fn assume(&mut self) -> bool {
        self.map.get("assume").is_some()
    }

    fn opaque(&mut self) -> bool {
        self.map.get("opaque").is_some()
    }

    fn fn_sig(&mut self) -> Option<surface::FnSig> {
        read_attr!(self, "ty", FnSig)
    }

    fn qualifiers(&mut self) -> Vec<surface::Qualifier> {
        read_all_attrs!(self, "qualifier", Qualifier)
    }

    fn refined_by(&mut self) -> Option<surface::Params> {
        read_attr!(self, "refined_by", RefinedBy)
    }

    fn field(&mut self) -> Option<surface::Ty> {
        read_attr!(self, "field", Field)
    }

    fn crate_config(&mut self) -> Option<config::CrateConfig> {
        read_attr!(self, "crate_config", CrateConfig)
    }
}

impl LiquidAttrKind {
    fn name(&self) -> &'static str {
        match self {
            LiquidAttrKind::Assume => "assume",
            LiquidAttrKind::Opaque => "opaque",
            LiquidAttrKind::FnSig(_) => "ty",
            LiquidAttrKind::RefinedBy(_) => "refined_by",
            LiquidAttrKind::Qualifier(_) => "qualifier",
            LiquidAttrKind::Field(_) => "field",
            LiquidAttrKind::CrateConfig(_) => "crate_config",
        }
    }
}

#[derive(Debug)]
struct CFGSetting {
    setting: String,
    span: Span,
}

#[derive(Debug)]
struct LiquidAttrCFG {
    map: HashMap<String, CFGSetting>,
}

macro_rules! try_read_setting {
    ($self:expr, $setting:literal, $type:ident, $default:expr) => {
        if let Some(CFGSetting { setting, span }) = $self.map.remove($setting) {
            let parse_result = setting.as_str().parse::<$type>();
            if parse_result.is_err() {
                Err(errors::CFGError {
                    span,
                    message: format!("incorrect type in value for setting `{}`", setting),
                })
            } else {
                Ok(parse_result.unwrap())
            }
        } else {
            Ok($default)
        }
    };
}

impl LiquidAttrCFG {
    // TODO: Ugly that we have to access the collector for error reporting
    fn parse_cfg(attr_item: &AttrItem) -> Result<Self, errors::CFGError> {
        let mut cfg = Self { map: HashMap::new() };
        let meta_item_kind = attr_item.meta_kind();
        match meta_item_kind {
            Some(MetaItemKind::List(items)) => {
                for item in items {
                    cfg.parse_cfg_item(&item)?;
                }
            }
            _ => {
                return Err(errors::CFGError {
                    span: attr_item.span(),
                    message: format!("bad syntax"),
                })
            }
        };

        //todo!();
        Ok(cfg)
    }

    fn parse_cfg_item(&mut self, nested_item: &NestedMetaItem) -> Result<(), errors::CFGError> {
        match nested_item {
            NestedMetaItem::MetaItem(item) => {
                let name = item.name_or_empty().to_ident_string();
                let span = item.span;
                if !name.is_empty() {
                    if self.map.get(&name).is_some() {
                        return Err(errors::CFGError {
                            span,
                            message: format!("duplicated setting: {}", name),
                        });
                    }

                    // TODO: support types of values other than strings
                    let value_str = item.value_str().map(|symbol| symbol.to_ident_string());

                    if !value_str.is_none() {
                        let value = value_str.unwrap();
                        let setting = CFGSetting { setting: value, span: item.span };
                        self.map.insert(name, setting);
                        return Ok(());
                    }
                }
                // Would have returned already if ok
                return Err(errors::CFGError { span, message: format!("bad setting name") });
            }
            _ => {
                return Err(errors::CFGError {
                    span: nested_item.span(),
                    message: format!("unsupported item"),
                })
            }
        }
    }

    fn try_into_crate_cfg(&mut self) -> Result<config::CrateConfig, errors::CFGError> {
        let log_dir = try_read_setting!(self, "log_dir", PathBuf, config::CONFIG.log_dir.clone())?;
        let dump_constraint =
            try_read_setting!(self, "dump_constraint", bool, config::CONFIG.dump_constraint)?;
        let dump_checker_trace =
            try_read_setting!(self, "dump_checker_trace", bool, config::CONFIG.dump_checker_trace)?;
        let check_asserts =
            try_read_setting!(self, "check_asserts", AssertBehavior, config::CONFIG.check_asserts)?;

        if let Some((name, setting)) = self.map.iter().next() {
            return Err(errors::CFGError {
                span: setting.span,
                message: format!("invalid crate cfg keyword `{}`", name),
            });
        }

        Ok(CrateConfig { log_dir, dump_constraint, dump_checker_trace, check_asserts })
    }
}

mod errors {
    use rustc_macros::SessionDiagnostic;
    use rustc_span::Span;

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct DuplicatedAttr {
        #[message = "duplicated attribute `{name}`"]
        pub span: Span,
        pub name: &'static str,
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct InvalidAttr {
        #[message = "invalid liquid attribute"]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct CFGError {
        #[message = "invalid liquid configuration attribute: {message}"]
        pub span: Span,
        pub message: String,
    }

    #[derive(SessionDiagnostic)]
    #[error = "LIQUID"]
    pub struct SyntaxErr {
        #[message = "Syntax Error: {msg}"]
        pub span: Span,
        pub msg: &'static str,
    }
}
