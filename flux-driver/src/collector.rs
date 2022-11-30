use std::{collections::HashMap, path::PathBuf};

use flux_common::{
    config::{self, AssertBehavior, CrateConfig},
    iter::IterExt,
};
use flux_errors::{FluxSession, ResultExt};
use flux_syntax::{
    parse_defn, parse_expr, parse_fn_surface_sig, parse_qualifier, parse_refined_by, parse_ty,
    parse_type_alias, parse_uif_def, parse_variant, surface, ParseResult,
};
use itertools::Itertools;
use rustc_ast::{
    tokenstream::TokenStream, AttrItem, AttrKind, Attribute, MacArgs, MetaItemKind, NestedMetaItem,
};
use rustc_errors::{ErrorGuaranteed, IntoDiagnostic};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{def_id::LocalDefId, EnumDef, ImplItemKind, Item, ItemKind, VariantData};
use rustc_middle::ty::{ScalarInt, TyCtxt};
use rustc_span::{Span, Symbol};

pub(crate) struct SpecCollector<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    specs: Specs,
    sess: &'a FluxSession,
    error_guaranteed: Option<ErrorGuaranteed>,
}

#[derive(PartialEq, Eq, Hash)]
pub enum IgnoreKey {
    /// Ignore the entire crate
    Crate,
    /// (Transitively) ignore the module named `LocalDefId`
    Module(LocalDefId),
}

/// Set of module (`LocalDefId`) that should be ignored by flux
pub type Ignores = FxHashSet<IgnoreKey>;

pub(crate) struct Specs {
    pub fns: FxHashMap<LocalDefId, FnSpec>,
    pub structs: FxHashMap<LocalDefId, surface::StructDef>,
    pub enums: FxHashMap<LocalDefId, surface::EnumDef>,
    pub qualifs: Vec<surface::Qualifier>,
    pub uifs: Vec<surface::UifDef>,
    pub aliases: surface::AliasMap,
    pub ignores: Ignores,
    pub consts: FxHashMap<LocalDefId, ConstSig>,
    pub crate_config: Option<config::CrateConfig>,
}

pub(crate) struct FnSpec {
    pub fn_sig: Option<surface::FnSig>,
    pub assume: bool,
}

#[derive(Debug)]
pub(crate) struct ConstSig {
    pub _ty: surface::ConstSig,
    pub val: i128,
}

impl<'tcx, 'a> SpecCollector<'tcx, 'a> {
    pub(crate) fn collect(
        tcx: TyCtxt<'tcx>,
        sess: &'a FluxSession,
    ) -> Result<Specs, ErrorGuaranteed> {
        let mut collector = Self { tcx, sess, specs: Specs::new(), error_guaranteed: None };

        collector.parse_crate_spec(tcx.hir().krate_attrs())?;

        let crate_items = tcx.hir_crate_items(());

        for item_id in crate_items.items() {
            let item = tcx.hir().item(item_id);
            let hir_id = item.hir_id();
            let attrs = tcx.hir().attrs(hir_id);
            let def_id = item.owner_id.def_id;
            let _ = match &item.kind {
                ItemKind::Fn(..) => collector.parse_fn_spec(def_id, attrs),
                ItemKind::Struct(data, ..) => collector.parse_struct_def(def_id, attrs, data),
                ItemKind::Enum(def, ..) => collector.parse_enum_def(def_id, attrs, def),
                ItemKind::Mod(..) => collector.parse_mod_spec(def_id, attrs),
                ItemKind::TyAlias(..) => collector.parse_tyalias_spec(def_id, attrs),
                ItemKind::Const(_ty, _body_id) => collector.parse_const_spec(item, attrs),
                _ => Ok(()),
            };
        }

        for impl_item_id in crate_items.impl_items() {
            let impl_item = tcx.hir().impl_item(impl_item_id);
            let def_id = impl_item.owner_id.def_id;
            if let ImplItemKind::Fn(..) = &impl_item.kind {
                let hir_id = impl_item.hir_id();
                let attrs = tcx.hir().attrs(hir_id);
                let _ = collector.parse_fn_spec(def_id, attrs);
            }
        }

        if let Some(e) = collector.error_guaranteed {
            Err(e)
        } else {
            Ok(collector.specs)
        }
    }

    fn parse_fn_spec(
        &mut self,
        def_id: LocalDefId,
        attrs: &[Attribute],
    ) -> Result<(), ErrorGuaranteed> {
        let mut attrs = self.parse_flux_attrs(attrs)?;
        self.report_dups(&attrs)?;
        // TODO(nilehmann) error if it has non-fun attrs

        let assume = attrs.assume();
        let fn_sig = attrs.fn_sig();

        self.specs.fns.insert(def_id, FnSpec { fn_sig, assume });
        Ok(())
    }

    fn parse_const_spec(
        &mut self,
        item: &Item,
        attrs: &[Attribute],
    ) -> Result<(), ErrorGuaranteed> {
        let mut attrs = self.parse_flux_attrs(attrs)?;
        self.report_dups(&attrs)?;

        let Some(_ty) = attrs.const_sig() else {
            return Ok(());
        };

        let def_id = item.owner_id.def_id;
        let span = item.span;
        let val = match eval_const(self.tcx, def_id) {
            Some(val) => val,
            None => return Err(self.emit_err(errors::InvalidConstant { span })),
        };

        let size = val.size();
        if let Ok(val) = val.try_to_int(size) {
            self.specs.consts.insert(def_id, ConstSig { _ty, val });
            Ok(())
        } else {
            Err(self.emit_err(errors::InvalidConstant { span }))
        }
    }
    fn parse_tyalias_spec(
        &mut self,
        _def_id: LocalDefId,
        attrs: &[Attribute],
    ) -> Result<(), ErrorGuaranteed> {
        let mut attrs = self.parse_flux_attrs(attrs)?;
        if let Some(alias) = attrs.alias() {
            self.specs.aliases.insert(alias.name, alias);
        }
        Ok(())
    }

    fn parse_mod_spec(
        &mut self,
        def_id: LocalDefId,
        attrs: &[Attribute],
    ) -> Result<(), ErrorGuaranteed> {
        let mut attrs = self.parse_flux_attrs(attrs)?;
        if attrs.ignore() {
            self.specs.ignores.insert(IgnoreKey::Module(def_id));
        }
        Ok(())
    }

    fn parse_enum_def(
        &mut self,
        def_id: LocalDefId,
        attrs: &[Attribute],
        def: &EnumDef,
    ) -> Result<(), ErrorGuaranteed> {
        let mut attrs = self.parse_flux_attrs(attrs)?;
        self.report_dups(&attrs)?;
        let refined_by = attrs.refined_by();
        let variants = def
            .variants
            .iter()
            .map(|variant| self.parse_variant_spec(self.tcx.hir().attrs(variant.id)))
            .try_collect_exhaust()?;

        let variants = match variants {
            Some(v) => v,
            None => vec![],
        };

        let invariants = attrs.invariants();

        self.specs
            .enums
            .insert(def_id, surface::EnumDef { def_id, refined_by, variants, invariants });
        Ok(())
    }

    fn parse_struct_def(
        &mut self,
        def_id: LocalDefId,
        attrs: &[Attribute],
        data: &VariantData,
    ) -> Result<(), ErrorGuaranteed> {
        let mut attrs = self.parse_flux_attrs(attrs)?;
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

        let invariants = attrs.invariants();

        self.specs
            .structs
            .insert(def_id, surface::StructDef { def_id, refined_by, fields, opaque, invariants });

        Ok(())
    }

    fn parse_crate_spec(&mut self, attrs: &[Attribute]) -> Result<(), ErrorGuaranteed> {
        // TODO(atgeller) error if non-crate attributes
        // TODO(atgeller) error if >1 cfg attributes

        let mut attrs = self.parse_flux_attrs(attrs)?;
        if attrs.ignore() {
            self.specs.ignores.insert(IgnoreKey::Crate);
        }

        let mut qualifiers = attrs.qualifiers();
        self.specs.qualifs.append(&mut qualifiers);

        let mut uif_defs = attrs.uif_defs();
        self.specs.uifs.append(&mut uif_defs);

        let crate_config = attrs.crate_config();
        self.specs.crate_config = crate_config;
        Ok(())
    }

    fn parse_field_spec(
        &mut self,
        attrs: &[Attribute],
    ) -> Result<Option<surface::Ty>, ErrorGuaranteed> {
        let mut attrs = self.parse_flux_attrs(attrs)?;
        self.report_dups(&attrs)?;
        Ok(attrs.field())
    }

    fn parse_variant_spec(
        &mut self,
        attrs: &[Attribute],
    ) -> Result<Option<surface::VariantDef>, ErrorGuaranteed> {
        let mut attrs = self.parse_flux_attrs(attrs)?;
        self.report_dups(&attrs)?;
        Ok(attrs.variant())
    }

    fn parse_flux_attrs(&mut self, attrs: &[Attribute]) -> Result<FluxAttrs, ErrorGuaranteed> {
        let attrs: Vec<_> = attrs
            .iter()
            .filter_map(|attr| {
                if let AttrKind::Normal(attr_item, ..) = &attr.kind {
                    match &attr_item.item.path.segments[..] {
                        [first, ..] if first.ident.as_str() == "flux" => Some(attr_item),
                        _ => None,
                    }
                } else {
                    None
                }
            })
            .map(|attr_item| self.parse_flux_attr(&attr_item.item))
            .try_collect_exhaust()?;

        Ok(FluxAttrs::new(attrs))
    }

    fn parse_flux_attr(&mut self, attr_item: &AttrItem) -> Result<FluxAttr, ErrorGuaranteed> {
        let segment = match &attr_item.path.segments[..] {
            [_, segment] => segment,
            _ => return Err(self.emit_err(errors::InvalidAttr { span: attr_item.span() })),
        };

        let kind = match (segment.ident.as_str(), &attr_item.args) {
            ("alias", MacArgs::Delimited(span, _, tokens)) => {
                let alias = self.parse(tokens.clone(), span.entire(), parse_type_alias)?;
                FluxAttrKind::TypeAlias(alias)
            }
            ("sig", MacArgs::Delimited(span, _, tokens)) => {
                let fn_sig = self.parse(tokens.clone(), span.entire(), parse_fn_surface_sig)?;
                FluxAttrKind::FnSig(fn_sig)
            }
            ("constant", MacArgs::Empty) => {
                FluxAttrKind::ConstSig(surface::ConstSig { span: attr_item.span() })
            }
            ("qualifier", MacArgs::Delimited(span, _, tokens)) => {
                let qualifer = self.parse(tokens.clone(), span.entire(), parse_qualifier)?;
                FluxAttrKind::Qualifier(qualifer)
            }
            ("dfn", MacArgs::Delimited(span, _, tokens)) => {
                let defn = self.parse(tokens.clone(), span.entire(), parse_defn)?;
                FluxAttrKind::Defn(defn)
            }
            ("ufn", MacArgs::Delimited(span, _, tokens)) => {
                let uif_def = self.parse(tokens.clone(), span.entire(), parse_uif_def)?;
                FluxAttrKind::UifDef(uif_def)
            }
            ("cfg", MacArgs::Delimited(_, _, _)) => {
                let crate_cfg = FluxAttrCFG::parse_cfg(attr_item)
                    .emit(self.sess)?
                    .try_into_crate_cfg()
                    .emit(self.sess)?;
                FluxAttrKind::CrateConfig(crate_cfg)
            }
            ("refined_by", MacArgs::Delimited(span, _, tokens)) => {
                let refined_by = self.parse(tokens.clone(), span.entire(), parse_refined_by)?;
                FluxAttrKind::RefinedBy(refined_by)
            }
            ("field", MacArgs::Delimited(span, _, tokens)) => {
                let ty = self.parse(tokens.clone(), span.entire(), parse_ty)?;
                FluxAttrKind::Field(ty)
            }
            ("variant", MacArgs::Delimited(span, _, tokens)) => {
                let variant = self.parse(tokens.clone(), span.entire(), parse_variant)?;
                FluxAttrKind::Variant(variant)
            }
            ("invariant", MacArgs::Delimited(span, _, tokens)) => {
                let invariant = self.parse(tokens.clone(), span.entire(), parse_expr)?;
                FluxAttrKind::Invariant(invariant)
            }
            ("ignore", MacArgs::Empty) => FluxAttrKind::Ignore,
            ("opaque", MacArgs::Empty) => FluxAttrKind::Opaque,
            ("assume", MacArgs::Empty) => FluxAttrKind::Assume,
            _ => return Err(self.emit_err(errors::InvalidAttr { span: attr_item.span() })),
        };
        Ok(FluxAttr { kind, span: attr_item.span() })
    }

    fn parse<T>(
        &mut self,
        tokens: TokenStream,
        input_span: Span,
        parser: impl FnOnce(TokenStream, Span) -> ParseResult<T>,
    ) -> Result<T, ErrorGuaranteed> {
        parser(tokens, input_span).map_err(|err| self.emit_err(errors::SyntaxErr::from(err)))
    }

    fn report_dups(&mut self, attrs: &FluxAttrs) -> Result<(), ErrorGuaranteed> {
        for (name, dups) in attrs.dups() {
            for attr in dups {
                if attr.allow_dups() {
                    continue;
                }
                self.error_guaranteed =
                    Some(self.emit_err(errors::DuplicatedAttr { span: attr.span, name }));
            }
        }
        if let Some(e) = self.error_guaranteed {
            Err(e)
        } else {
            Ok(())
        }
    }

    fn emit_err(&mut self, err: impl IntoDiagnostic<'a>) -> ErrorGuaranteed {
        let e = self.sess.emit_err(err);
        self.error_guaranteed = Some(e);
        e
    }
}

fn eval_const(tcx: TyCtxt, did: LocalDefId) -> Option<ScalarInt> {
    let const_result = tcx.const_eval_poly(did.to_def_id());
    if let Ok(const_val) = const_result {
        return const_val.try_to_scalar_int();
    }
    None
}

impl Specs {
    fn new() -> Specs {
        Specs {
            fns: FxHashMap::default(),
            structs: FxHashMap::default(),
            enums: FxHashMap::default(),
            qualifs: Vec::default(),
            uifs: Vec::default(),
            aliases: FxHashMap::default(),
            ignores: FxHashSet::default(),
            consts: FxHashMap::default(),
            crate_config: None,
        }
    }
}

#[derive(Debug)]
struct FluxAttrs {
    map: HashMap<&'static str, Vec<FluxAttr>>,
}

#[derive(Debug)]
struct FluxAttr {
    kind: FluxAttrKind,
    span: Span,
}

#[derive(Debug)]
enum FluxAttrKind {
    Assume,
    Opaque,
    FnSig(surface::FnSig),
    RefinedBy(surface::RefinedBy),
    Qualifier(surface::Qualifier),
    Defn(surface::Defn),
    UifDef(surface::UifDef),
    TypeAlias(surface::Alias),
    Field(surface::Ty),
    Variant(surface::VariantDef),
    ConstSig(surface::ConstSig),
    CrateConfig(config::CrateConfig),
    Invariant(surface::Expr),
    Ignore,
}

macro_rules! attr_name {
    ($kind:ident) => {{
        let _ = FluxAttrKind::$kind;
        stringify!($kind)
    }};
}

macro_rules! read_flag {
    ($self:expr, $kind:ident) => {{
        $self.map.get(attr_name!($kind)).is_some()
    }};
}

macro_rules! read_attrs {
    ($self:expr, $kind:ident) => {
        $self
            .map
            .remove(attr_name!($kind))
            .unwrap_or_else(|| vec![])
            .into_iter()
            .filter_map(|attr| if let FluxAttrKind::$kind(v) = attr.kind { Some(v) } else { None })
            .collect::<Vec<_>>()
    };
}

macro_rules! read_attr {
    ($self:expr, $kind:ident) => {
        read_attrs!($self, $kind).pop()
    };
}

impl FluxAttr {
    pub fn allow_dups(&self) -> bool {
        matches!(&self.kind, FluxAttrKind::Invariant(..))
    }
}

impl FluxAttrs {
    fn new(attrs: Vec<FluxAttr>) -> Self {
        FluxAttrs { map: attrs.into_iter().into_group_map_by(|attr| attr.kind.name()) }
    }

    fn dups(&self) -> impl Iterator<Item = (&'static str, &[FluxAttr])> {
        self.map
            .iter()
            .filter(|(_, attrs)| attrs.len() > 1)
            .map(|(name, attrs)| (*name, &attrs[1..]))
    }

    fn assume(&mut self) -> bool {
        read_flag!(self, Assume)
    }

    fn ignore(&mut self) -> bool {
        read_flag!(self, Ignore)
    }

    fn opaque(&mut self) -> bool {
        read_flag!(self, Opaque)
    }

    fn fn_sig(&mut self) -> Option<surface::FnSig> {
        read_attr!(self, FnSig)
    }

    fn const_sig(&mut self) -> Option<surface::ConstSig> {
        read_attr!(self, ConstSig)
    }

    fn qualifiers(&mut self) -> Vec<surface::Qualifier> {
        read_attrs!(self, Qualifier)
    }

    fn uif_defs(&mut self) -> Vec<surface::UifDef> {
        read_attrs!(self, UifDef)
    }

    fn alias(&mut self) -> Option<surface::Alias> {
        read_attr!(self, TypeAlias)
    }

    fn refined_by(&mut self) -> Option<surface::RefinedBy> {
        read_attr!(self, RefinedBy)
    }

    fn field(&mut self) -> Option<surface::Ty> {
        read_attr!(self, Field)
    }

    fn variant(&mut self) -> Option<surface::VariantDef> {
        read_attr!(self, Variant)
    }

    fn crate_config(&mut self) -> Option<config::CrateConfig> {
        read_attr!(self, CrateConfig)
    }

    fn invariants(&mut self) -> Vec<surface::Expr> {
        read_attrs!(self, Invariant)
    }
}

impl FluxAttrKind {
    fn name(&self) -> &'static str {
        match self {
            FluxAttrKind::Assume => attr_name!(Assume),
            FluxAttrKind::Opaque => attr_name!(Opaque),
            FluxAttrKind::FnSig(_) => attr_name!(FnSig),
            FluxAttrKind::ConstSig(_) => attr_name!(ConstSig),
            FluxAttrKind::RefinedBy(_) => attr_name!(RefinedBy),
            FluxAttrKind::Qualifier(_) => attr_name!(Qualifier),
            FluxAttrKind::Defn(_) => attr_name!(Defn),
            FluxAttrKind::Field(_) => attr_name!(Field),
            FluxAttrKind::Variant(_) => attr_name!(Variant),
            FluxAttrKind::TypeAlias(_) => attr_name!(TypeAlias),
            FluxAttrKind::CrateConfig(_) => attr_name!(CrateConfig),
            FluxAttrKind::Ignore => attr_name!(Ignore),
            FluxAttrKind::UifDef(_) => attr_name!(UifDef),
            FluxAttrKind::Invariant(_) => attr_name!(Invariant),
        }
    }
}

#[derive(Debug)]
struct CFGSetting {
    setting: String,
    span: Span,
}

#[derive(Debug)]
struct FluxAttrCFG {
    map: HashMap<String, CFGSetting>,
}

macro_rules! try_read_setting {
    ($self:expr, $setting:literal, $type:ident, $default:expr) => {
        if let Some(CFGSetting { setting, span }) = $self.map.remove($setting) {
            let parse_result = setting.as_str().parse::<$type>();
            if parse_result.is_err() {
                Err(errors::CFGError {
                    span,
                    message: format!(
                        "incorrect type in value for setting `{}`, expected {}",
                        $setting,
                        stringify!($type)
                    ),
                })
            } else {
                Ok(parse_result.unwrap())
            }
        } else {
            Ok($default)
        }
    };
}

impl FluxAttrCFG {
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
                    message: "bad syntax".to_string(),
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
                            message: format!("duplicated setting `{name}`"),
                        });
                    }

                    // TODO: support types of values other than strings
                    let value = item
                        .value_str()
                        .map(Symbol::to_ident_string)
                        .ok_or_else(|| {
                            errors::CFGError { span, message: "unsupported value".to_string() }
                        })?;

                    let setting = CFGSetting { setting: value, span: item.span };
                    self.map.insert(name, setting);
                    return Ok(());
                }
                Err(errors::CFGError { span, message: "bad setting name".to_string() })
            }
            NestedMetaItem::Literal(_) => {
                Err(errors::CFGError {
                    span: nested_item.span(),
                    message: "unsupported item".to_string(),
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
                message: format!("invalid crate cfg keyword `{name}`"),
            });
        }

        Ok(CrateConfig { log_dir, dump_constraint, dump_checker_trace, check_asserts })
    }
}

mod errors {
    use flux_macros::Diagnostic;
    use rustc_span::Span;

    #[derive(Diagnostic)]
    #[diag(parse::duplicated_attr, code = "FLUX")]
    pub struct DuplicatedAttr {
        #[primary_span]
        pub span: Span,
        pub name: &'static str,
    }

    #[derive(Diagnostic)]
    #[diag(parse::invalid_attr, code = "FLUX")]
    pub struct InvalidAttr {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(parse::invalid_constant, code = "FLUX")]
    pub struct InvalidConstant {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(parse::cfg_error, code = "FLUX")]
    pub struct CFGError {
        #[primary_span]
        pub span: Span,
        pub message: String,
    }

    #[derive(Diagnostic)]
    #[diag(parse::syntax_err, code = "FLUX")]
    pub struct SyntaxErr {
        #[primary_span]
        pub span: Span,
        pub msg: &'static str,
    }

    impl From<flux_syntax::ParseError> for SyntaxErr {
        fn from(err: flux_syntax::ParseError) -> Self {
            use flux_syntax::ParseErrorKind;
            let msg = match err.kind {
                ParseErrorKind::UnexpectedEOF => "type annotation ended unexpectedly",
                ParseErrorKind::UnexpectedToken => "unexpected token",
                ParseErrorKind::IntTooLarge => "integer literal is too large",
            };

            SyntaxErr { span: err.span, msg }
        }
    }
}
