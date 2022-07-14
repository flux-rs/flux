use std::{
    collections::{HashMap, HashSet},
    path::PathBuf,
};

use flux_common::{
    config::{self, AssertBehavior, CrateConfig},
    iter::IterExt,
};
use flux_errors::FluxSession;
use flux_middle::rustc::ty::{rustc_substs_trait_ref_key, TraitImplMap};
use flux_syntax::{
    parse_fn_surface_sig, parse_qualifier, parse_refined_by, parse_ty, parse_type_alias, surface,
    ParseErrorKind, ParseResult,
};
use itertools::Itertools;
use rustc_ast::{
    tokenstream::TokenStream, AttrItem, AttrKind, Attribute, MacArgs, MetaItemKind, NestedMetaItem,
};
use rustc_errors::ErrorGuaranteed;
use rustc_hash::FxHashMap;
use rustc_hir::{
    def_id::{DefId, LocalDefId},
    ImplItem, ImplItemKind, ItemKind, VariantData,
};
use rustc_middle::ty::TyCtxt;
use rustc_session::SessionDiagnostic;
use rustc_span::Span;

pub(crate) struct SpecCollector<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    specs: Specs,
    sess: &'a FluxSession,
    error_guaranteed: Option<ErrorGuaranteed>,
}

pub(crate) struct Specs {
    pub fns: FxHashMap<LocalDefId, FnSpec>,
    pub structs: FxHashMap<LocalDefId, surface::StructDef>,
    pub enums: FxHashMap<LocalDefId, surface::EnumDef>,
    pub qualifs: Vec<surface::Qualifier>,
    pub aliases: surface::AliasMap,
    pub crate_config: Option<config::CrateConfig>,
    pub trait_impls: TraitImplMap,
}

pub(crate) struct FnSpec {
    pub fn_sig: Option<surface::FnSig>,
    pub assume: bool,
}

impl<'tcx, 'a> SpecCollector<'tcx, 'a> {
    pub(crate) fn collect(
        tcx: TyCtxt<'tcx>,
        sess: &'a FluxSession,
    ) -> Result<Specs, ErrorGuaranteed> {
        let mut collector = Self { tcx, sess, specs: Specs::new(), error_guaranteed: None };

        let mut trait_impl_ids: HashSet<DefId> = HashSet::new();

        collector.parse_crate_spec(tcx.hir().krate_attrs())?;

        let crate_items = tcx.hir_crate_items(());

        for item_id in crate_items.items() {
            let item = tcx.hir().item(item_id);
            match &item.kind {
                ItemKind::Fn(..) => {
                    let hir_id = item.hir_id();
                    let attrs = tcx.hir().attrs(hir_id);
                    let _ = collector.parse_fn_spec(item.def_id, attrs);
                }
                ItemKind::Struct(data, ..) => {
                    let hir_id = item.hir_id();
                    let attrs = tcx.hir().attrs(hir_id);
                    let _ = collector.parse_struct_def(item.def_id, attrs, data);
                }
                ItemKind::Enum(..) => {
                    let hir_id = item.hir_id();
                    let attrs = tcx.hir().attrs(hir_id);
                    let _ = collector.parse_enum_def(item.def_id, attrs);
                }
                ItemKind::Mod(..) => {
                    // TODO: Parse mod level attributes
                }
                ItemKind::TyAlias(..) => {
                    let hir_id = item.hir_id();
                    let attrs = tcx.hir().attrs(hir_id);
                    let _ = collector.parse_tyalias_spec(item.def_id, attrs);
                }
                _ => {}
            }
        }

        for impl_item_id in crate_items.impl_items() {
            let impl_item = tcx.hir().impl_item(impl_item_id);
            if let ImplItemKind::Fn(..) = &impl_item.kind {
                let hir_id = impl_item.hir_id();
                let attrs = tcx.hir().attrs(hir_id);
                let _ = collector.parse_fn_spec(impl_item.def_id, attrs);
                collector.parse_trait_impl(impl_item, &mut trait_impl_ids);
            }
        }

        println!("TRACE: trait_impls {:#?}", collector.specs.trait_impls);

        if let Some(e) = collector.error_guaranteed {
            Err(e)
        } else {
            Ok(collector.specs)
        }
    }

    // fn trait_ref_key(&self, trait_ref: rustc_middle::ty::TraitRef) -> Option<TraitRefKey> {
    //     // let substs = trait_ref.substs;
    //     rustc_substs_trait_ref_key(trait_ref.substs)
    // }

    fn parse_trait_impl(&mut self, impl_item: &ImplItem, trait_impl_ids: &mut HashSet<DefId>) {
        let impl_def_id = impl_item.def_id;
        if let Some(real_impl_def_id) = self.tcx.impl_of_method(impl_def_id.to_def_id()) {
            if !trait_impl_ids.contains(&real_impl_def_id) {
                trait_impl_ids.insert(real_impl_def_id);
                if let Some(trait_ref) = self.tcx.impl_trait_ref(real_impl_def_id) {
                    if let Some(key) = rustc_substs_trait_ref_key(trait_ref.substs) {
                        let impl_ids = self.tcx.impl_item_implementor_ids(real_impl_def_id);
                        for (trait_f, trait_f_ty) in impl_ids {
                            self.specs.trait_impls.insert((*trait_f, key), *trait_f_ty);
                        }
                    }
                }
            }
        }
        // if we have already handled this impl then move on
        // // let trait_id = tcx.trait_id_of_impl(real_impl_def_id)?;
        // let mega = tcx.impl_item_implementor_ids(real_impl_def_id);
        // println!("TRACE: TRAIT-IMPL {real_impl_def_id:?}, {mega:#?}");
        // let trait_ref = tcx.impl_trait_ref(real_impl_def_id)?;
        // println!(
        //     "TRACE: TRAIT_REF def_id = {:?}, substs = {:?}",
        //     trait_ref.def_id, trait_ref.substs
        // );
        // // println!("TRACE: PUSH ME {impl_def_id:?}, real_impl_def_id = {real_impl_def_id:?}");
        // // let impl_trait_def_id = Self::impl_item_trait_ref(tcx, impl_item);
        // // println!("TRACE: collector {impl_def_id:?}, trait_def = {impl_trait_def_id:?}");
        // // real_impl_def_id.map(|id| impl_ids.insert(id));
    }

    /// Returns the `DefId` of the trait being implemented by the `hir_id`
    fn _impl_item_trait_ref(tcx: TyCtxt<'tcx>, impl_item: &ImplItem) -> Option<DefId> {
        let hir_id = impl_item.hir_id();
        let parent = tcx.hir().get_parent_node(hir_id);

        let parent_node = tcx.hir().find(parent)?;

        match parent_node {
            rustc_hir::Node::Item(parent_item) => {
                match parent_item.kind {
                    ItemKind::Impl(parent_impl) => {
                        let trait_ref = parent_impl.of_trait.as_ref()?;
                        let self_ty = parent_impl.self_ty;
                        let trait_def_id = trait_ref.trait_def_id()?;
                        println!(
                            "TRACE: impl_item_trait_ref `{trait_def_id:?}` has `{self_ty:#?}`"
                        );
                        Some(trait_def_id)
                    }
                    _ => None,
                }
            }
            _ => None,
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

    fn parse_tyalias_spec(
        &mut self,
        _def_id: LocalDefId,
        attrs: &[Attribute],
    ) -> Result<(), ErrorGuaranteed> {
        let mut attrs = self.parse_flux_attrs(attrs)?;
        if let Some(alias) = attrs.alias() {
            // println!("ALIAS: insert {:?} -> {:?}", alias.name, alias);
            self.specs.aliases.insert(alias.name, alias);
        }
        Ok(())
    }

    fn parse_enum_def(
        &mut self,
        def_id: LocalDefId,
        attrs: &[Attribute],
    ) -> Result<(), ErrorGuaranteed> {
        let mut attrs = self.parse_flux_attrs(attrs)?;
        self.report_dups(&attrs)?;
        let opaque = attrs.opaque();
        let refined_by = attrs.refined_by();
        self.specs
            .enums
            .insert(def_id, surface::EnumDef { def_id, refined_by, opaque });
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

        self.specs
            .structs
            .insert(def_id, surface::StructDef { def_id, refined_by, fields, opaque });

        Ok(())
    }

    fn parse_crate_spec(&mut self, attrs: &[Attribute]) -> Result<(), ErrorGuaranteed> {
        // TODO(atgeller) error if non-crate attributes
        // TODO(atgeller) error if >1 cfg attributes

        let mut attrs = self.parse_flux_attrs(attrs)?;
        let mut qualifiers = attrs.qualifiers();
        self.specs.qualifs.append(&mut qualifiers);
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

    fn parse_flux_attrs(&mut self, attrs: &[Attribute]) -> Result<FluxAttrs, ErrorGuaranteed> {
        let attrs: Vec<_> = attrs
            .iter()
            .filter_map(|attr| {
                if let AttrKind::Normal(attr_item, ..) = &attr.kind {
                    match &attr_item.path.segments[..] {
                        [first, ..] if first.ident.as_str() == "flux" => Some(attr_item),
                        _ => None,
                    }
                } else {
                    None
                }
            })
            .map(|attr_item| self.parse_flux_attr(attr_item))
            .try_collect_exhaust()?;

        Ok(FluxAttrs::new(attrs))
    }

    fn parse_flux_attr(&mut self, attr_item: &AttrItem) -> Result<FluxAttr, ErrorGuaranteed> {
        let segment = match &attr_item.path.segments[..] {
            [_, segment] => segment,
            _ => return self.emit_err(errors::InvalidAttr { span: attr_item.span() }),
        };

        let kind = match (segment.ident.as_str(), &attr_item.args) {
            ("alias", MacArgs::Delimited(span, _, tokens)) => {
                let ty_alias = self.parse(tokens.clone(), span.entire(), parse_type_alias)?;
                // println!("ALIAS: {:?}", ty_alias);
                FluxAttrKind::TypeAlias(ty_alias)
            }
            ("sig", MacArgs::Delimited(span, _, tokens)) => {
                let fn_sig = self.parse(tokens.clone(), span.entire(), parse_fn_surface_sig)?;
                FluxAttrKind::FnSig(fn_sig)
            }
            ("qualifier", MacArgs::Delimited(span, _, tokens)) => {
                let qualifer = self.parse(tokens.clone(), span.entire(), parse_qualifier)?;
                FluxAttrKind::Qualifier(qualifer)
            }
            ("cfg", MacArgs::Delimited(_, _, _)) => {
                match FluxAttrCFG::parse_cfg(attr_item) {
                    Err(error) => return self.emit_err(error),
                    Ok(mut cfg) => {
                        match cfg.try_into_crate_cfg() {
                            Err(error) => return self.emit_err(error),
                            Ok(crate_cfg) => FluxAttrKind::CrateConfig(crate_cfg),
                        }
                    }
                }
            }
            ("refined_by", MacArgs::Delimited(span, _, tokens)) => {
                let refined_by = self.parse(tokens.clone(), span.entire(), parse_refined_by)?;
                FluxAttrKind::RefinedBy(refined_by)
            }
            ("field", MacArgs::Delimited(span, _, tokens)) => {
                let ty = self.parse(tokens.clone(), span.entire(), parse_ty)?;
                FluxAttrKind::Field(ty)
            }
            ("opaque", MacArgs::Empty) => FluxAttrKind::Opaque,
            ("assume", MacArgs::Empty) => FluxAttrKind::Assume,
            _ => return self.emit_err(errors::InvalidAttr { span: attr_item.span() }),
        };
        Ok(FluxAttr { kind, span: attr_item.span() })
    }

    fn parse<T>(
        &mut self,
        tokens: TokenStream,
        input_span: Span,
        parser: impl FnOnce(TokenStream, Span) -> ParseResult<T>,
    ) -> Result<T, ErrorGuaranteed> {
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

    fn report_dups(&mut self, attrs: &FluxAttrs) -> Result<(), ErrorGuaranteed> {
        for (name, dups) in attrs.dups() {
            for attr in dups {
                self.error_guaranteed = Some(
                    self.sess
                        .emit_err(errors::DuplicatedAttr { span: attr.span, name }),
                );
            }
        }
        if let Some(e) = self.error_guaranteed {
            Err(e)
        } else {
            Ok(())
        }
    }

    fn emit_err<T>(&mut self, err: impl SessionDiagnostic<'a>) -> Result<T, ErrorGuaranteed> {
        let e = self.sess.emit_err(err);
        self.error_guaranteed = Some(e);
        Err(e)
    }
}

impl Specs {
    fn new() -> Specs {
        Specs {
            fns: FxHashMap::default(),
            structs: FxHashMap::default(),
            enums: FxHashMap::default(),
            qualifs: Vec::default(),
            aliases: FxHashMap::default(),
            crate_config: None,
            trait_impls: FxHashMap::default(),
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
    RefinedBy(surface::Params),
    Qualifier(surface::Qualifier),
    TypeAlias(surface::Alias),
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
                |attr| if let FluxAttrKind::$kind(sig) = attr.kind { Some(sig) } else { None },
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
                |attr| if let FluxAttrKind::$kind(sig) = attr.kind { Some(sig) } else { None },
            )
            .collect()
    };
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

    fn alias(&mut self) -> Option<surface::Alias> {
        read_attr!(self, "alias", TypeAlias)
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

impl FluxAttrKind {
    fn name(&self) -> &'static str {
        match self {
            FluxAttrKind::Assume => "assume",
            FluxAttrKind::Opaque => "opaque",
            FluxAttrKind::FnSig(_) => "ty",
            FluxAttrKind::RefinedBy(_) => "refined_by",
            FluxAttrKind::Qualifier(_) => "qualifier",
            FluxAttrKind::Field(_) => "field",
            FluxAttrKind::TypeAlias(_) => "alias",
            FluxAttrKind::CrateConfig(_) => "crate_config",
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
                            message: format!("duplicated setting `{}`", name),
                        });
                    }

                    // TODO: support types of values other than strings
                    let value_str = item.value_str().map(|symbol| symbol.to_ident_string());

                    if let Some(value) = value_str {
                        let setting = CFGSetting { setting: value, span: item.span };
                        self.map.insert(name, setting);
                        return Ok(());
                    }
                }
                Err(errors::CFGError { span, message: "bad setting name".to_string() })
            }
            _ => {
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
    #[error(code = "FLUX", slug = "parse-duplicated-attr")]
    pub struct DuplicatedAttr {
        #[primary_span]
        pub span: Span,
        pub name: &'static str,
    }

    #[derive(SessionDiagnostic)]
    #[error(code = "FLUX", slug = "parse-invalid-attr")]
    pub struct InvalidAttr {
        #[primary_span]
        pub span: Span,
    }

    #[derive(SessionDiagnostic)]
    #[error(code = "FLUX", slug = "parse-cfg-error")]
    pub struct CFGError {
        #[primary_span]
        pub span: Span,
        pub message: String,
    }

    #[derive(SessionDiagnostic)]
    #[error(code = "FLUX", slug = "parse-syntax-err")]
    pub struct SyntaxErr {
        #[primary_span]
        pub span: Span,
        pub msg: &'static str,
    }
}
