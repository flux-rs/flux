use std::collections::HashMap;

use flux_common::iter::IterExt;
use flux_config::{self as config, CrateConfig};
use flux_errors::{FluxSession, ResultExt};
use flux_middle::{const_eval::scalar_int_to_rty_constant, rty::Constant};
use flux_syntax::{
    parse_expr, parse_flux_item, parse_fn_surface_sig, parse_qual_names, parse_refined_by,
    parse_ty, parse_type_alias, parse_variant, surface, ParseResult,
};
use itertools::Itertools;
use rustc_ast::{
    tokenstream::TokenStream, AttrArgs, AttrItem, AttrKind, Attribute, MetaItemKind, NestedMetaItem,
};
use rustc_errors::{ErrorGuaranteed, IntoDiagnostic};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{
    def_id::{DefId, LocalDefId},
    EnumDef, ImplItemKind, Item, ItemKind, OwnerId, VariantData,
};
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
    pub fn_sigs: FxHashMap<OwnerId, FnSpec>,
    pub structs: FxHashMap<OwnerId, surface::StructDef>,
    pub enums: FxHashMap<OwnerId, surface::EnumDef>,
    pub qualifs: Vec<surface::Qualifier>,
    pub func_defs: Vec<surface::FuncDef>,
    pub sort_decls: Vec<surface::SortDecl>,
    pub aliases: FxHashMap<OwnerId, Option<surface::TyAlias>>,
    pub ignores: Ignores,
    pub consts: FxHashMap<LocalDefId, ConstSig>,
    pub crate_config: Option<config::CrateConfig>,
    pub extern_specs: FxHashMap<DefId, LocalDefId>,
}

pub(crate) struct FnSpec {
    pub fn_sig: Option<surface::FnSig>,
    pub trusted: bool,
    pub qual_names: Option<surface::QualNames>,
}

#[derive(Debug)]
pub(crate) struct ConstSig {
    pub _ty: surface::ConstSig,
    pub val: Constant,
}

macro_rules! attr_name {
    ($kind:ident) => {{
        let _ = FluxAttrKind::$kind;
        stringify!($kind)
    }};
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
            let owner_id = item.owner_id;
            let _ = match &item.kind {
                ItemKind::Fn(..) => collector.parse_fn_spec(owner_id, attrs),
                ItemKind::Struct(data, ..) => collector.parse_struct_def(owner_id, attrs, data),
                ItemKind::Enum(def, ..) => collector.parse_enum_def(owner_id, attrs, def),
                ItemKind::Mod(..) => collector.parse_mod_spec(owner_id.def_id, attrs),
                ItemKind::TyAlias(..) => collector.parse_tyalias_spec(owner_id, attrs),
                ItemKind::Const(_ty, _body_id) => collector.parse_const_spec(item, attrs),
                _ => Ok(()),
            };
        }

        for impl_item_id in crate_items.impl_items() {
            let impl_item = tcx.hir().impl_item(impl_item_id);
            let owner_id = impl_item.owner_id;
            if let ImplItemKind::Fn(..) = &impl_item.kind {
                let hir_id = impl_item.hir_id();
                let attrs = tcx.hir().attrs(hir_id);
                let _ = collector.parse_fn_spec(owner_id, attrs);
            }
        }

        if let Some(e) = collector.error_guaranteed {
            Err(e)
        } else {
            Ok(collector.specs)
        }
    }

    fn parse_crate_spec(&mut self, attrs: &[Attribute]) -> Result<(), ErrorGuaranteed> {
        // TODO(atgeller) error if non-crate attributes
        // TODO(atgeller) error if >1 cfg attributes

        let mut attrs = self.parse_flux_attrs(attrs)?;
        if attrs.ignore() {
            self.specs.ignores.insert(IgnoreKey::Crate);
        }

        self.specs.extend_items(attrs.items());

        let crate_config = attrs.crate_config();
        self.specs.crate_config = crate_config;
        Ok(())
    }

    fn parse_mod_spec(
        &mut self,
        def_id: LocalDefId,
        attrs: &[Attribute],
    ) -> Result<(), ErrorGuaranteed> {
        let mut attrs = self.parse_flux_attrs(attrs)?;
        self.specs.extend_items(attrs.items());
        if attrs.ignore() {
            self.specs.ignores.insert(IgnoreKey::Module(def_id));
        }
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
        let Some(val) = eval_const(self.tcx, def_id) else {
            return Err(self.emit_err(errors::InvalidConstant { span }));
        };

        let ty = self.tcx.type_of(def_id).instantiate_identity();
        if let Some(val) = scalar_int_to_rty_constant(self.tcx, val, ty) {
            self.specs.consts.insert(def_id, ConstSig { _ty, val });
            Ok(())
        } else {
            Err(self.emit_err(errors::InvalidConstant { span }))
        }
    }

    fn parse_tyalias_spec(
        &mut self,
        owner_id: OwnerId,
        attrs: &[Attribute],
    ) -> Result<(), ErrorGuaranteed> {
        let mut attrs = self.parse_flux_attrs(attrs)?;
        self.specs.aliases.insert(owner_id, attrs.alias());
        Ok(())
    }

    fn parse_struct_def(
        &mut self,
        owner_id: OwnerId,
        attrs: &[Attribute],
        data: &VariantData,
    ) -> Result<(), ErrorGuaranteed> {
        let mut attrs = self.parse_flux_attrs(attrs)?;
        self.report_dups(&attrs)?;
        // TODO(nilehmann) error if it has non-struct attrs

        let mut opaque = attrs.opaque();

        let refined_by = attrs.refined_by();

        let fields = data
            .fields()
            .iter()
            .map(|field| self.parse_field_spec(field, opaque))
            .try_collect_exhaust()?;

        let invariants = attrs.invariants();

        if attrs.extern_spec() {
            // extern_spec dummy structs are always opaque because they contain
            // one field: the external struct they are meant to represent.
            opaque = true;
            let extern_def_id =
                self.extract_extern_def_id_from_extern_spec_struct(owner_id.def_id, data)?;
            self.specs
                .extern_specs
                .insert(extern_def_id, owner_id.def_id);
        }

        self.specs
            .structs
            .insert(owner_id, surface::StructDef { refined_by, fields, opaque, invariants });

        Ok(())
    }

    fn parse_field_spec(
        &mut self,
        field: &rustc_hir::FieldDef,
        opaque: bool,
    ) -> Result<Option<surface::Ty>, ErrorGuaranteed> {
        let attrs = self.tcx.hir().attrs(field.hir_id);
        let mut attrs = self.parse_flux_attrs(attrs)?;
        self.report_dups(&attrs)?;
        if opaque && let Some(span) = attrs.contains(attr_name!(Field)) {
            return Err(self.emit_err(errors::AttrOnOpaque::new(span, field)))
        }
        Ok(attrs.field())
    }

    fn parse_enum_def(
        &mut self,
        owner_id: OwnerId,
        attrs: &[Attribute],
        enum_def: &EnumDef,
    ) -> Result<(), ErrorGuaranteed> {
        let mut attrs = self.parse_flux_attrs(attrs)?;
        self.report_dups(&attrs)?;
        let refined_by = attrs.refined_by();
        let variants = enum_def
            .variants
            .iter()
            .map(|variant| self.parse_variant(variant, refined_by.is_some()))
            .try_collect_exhaust()?;

        let invariants = attrs.invariants();

        self.specs
            .enums
            .insert(owner_id, surface::EnumDef { refined_by, variants, invariants });
        Ok(())
    }

    fn parse_variant(
        &mut self,
        hir_variant: &rustc_hir::Variant,
        has_refined_by: bool,
    ) -> Result<Option<surface::VariantDef>, ErrorGuaranteed> {
        let attrs = self.tcx.hir().attrs(hir_variant.hir_id);
        let mut attrs = self.parse_flux_attrs(attrs)?;
        self.report_dups(&attrs)?;

        let variant = attrs.variant();

        if variant.is_none() && has_refined_by {
            return Err(self.emit_err(errors::MissingVariant::new(hir_variant.span)));
        }

        Ok(variant)
    }

    fn parse_fn_spec(
        &mut self,
        owner_id: OwnerId,
        attrs: &[Attribute],
    ) -> Result<(), ErrorGuaranteed> {
        let mut attrs = self.parse_flux_attrs(attrs)?;
        self.report_dups(&attrs)?;
        // TODO(nilehmann) error if it has non-fun attrs

        let mut trusted = attrs.trusted();
        let fn_sig = attrs.fn_sig();
        let qual_names = attrs.qual_names();
        if attrs.extern_spec() {
            if fn_sig.is_none() {
                return Err(self.emit_err(errors::MissingFnSigForExternSpec {
                    span: self.tcx.def_span(owner_id),
                }));
            }
            let extern_def_id = self.extract_extern_def_id_from_extern_spec_fn(owner_id.def_id)?;
            self.specs
                .extern_specs
                .insert(extern_def_id, owner_id.def_id);
            // We should never check an extern spec (it will infinitely recurse)
            trusted = true;
        }
        self.specs
            .fn_sigs
            .insert(owner_id, FnSpec { fn_sig, trusted, qual_names });
        Ok(())
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
        let [_, segment] = &attr_item.path.segments[..] else {
            return Err(self.emit_err(errors::InvalidAttr { span: attr_item.span() }));
        };

        let kind = match (segment.ident.as_str(), &attr_item.args) {
            ("alias", AttrArgs::Delimited(dargs)) => {
                let alias =
                    self.parse(dargs.tokens.clone(), dargs.dspan.entire(), parse_type_alias)?;
                FluxAttrKind::TypeAlias(alias)
            }
            ("sig", AttrArgs::Delimited(dargs)) => {
                let fn_sig =
                    self.parse(dargs.tokens.clone(), dargs.dspan.entire(), parse_fn_surface_sig)?;
                FluxAttrKind::FnSig(fn_sig)
            }
            ("qualifiers", AttrArgs::Delimited(dargs)) => {
                let qualifiers =
                    self.parse(dargs.tokens.clone(), dargs.dspan.entire(), parse_qual_names)?;
                FluxAttrKind::QualNames(qualifiers)
            }
            ("constant", AttrArgs::Empty) => {
                FluxAttrKind::ConstSig(surface::ConstSig { span: attr_item.span() })
            }
            ("defs", AttrArgs::Delimited(dargs)) => {
                let items =
                    self.parse(dargs.tokens.clone(), dargs.dspan.entire(), parse_flux_item)?;
                FluxAttrKind::Items(items)
            }
            ("cfg", AttrArgs::Delimited(..)) => {
                let crate_cfg = FluxAttrCFG::parse_cfg(attr_item)
                    .emit(self.sess)?
                    .try_into_crate_cfg()
                    .emit(self.sess)?;
                FluxAttrKind::CrateConfig(crate_cfg)
            }
            ("refined_by", AttrArgs::Delimited(dargs)) => {
                let refined_by =
                    self.parse(dargs.tokens.clone(), dargs.dspan.entire(), parse_refined_by)?;
                FluxAttrKind::RefinedBy(refined_by)
            }
            ("field", AttrArgs::Delimited(dargs)) => {
                let ty = self.parse(dargs.tokens.clone(), dargs.dspan.entire(), parse_ty)?;
                FluxAttrKind::Field(ty)
            }
            ("variant", AttrArgs::Delimited(dargs)) => {
                let variant =
                    self.parse(dargs.tokens.clone(), dargs.dspan.entire(), parse_variant)?;
                FluxAttrKind::Variant(variant)
            }
            ("invariant", AttrArgs::Delimited(dargs)) => {
                let invariant =
                    self.parse(dargs.tokens.clone(), dargs.dspan.entire(), parse_expr)?;
                FluxAttrKind::Invariant(invariant)
            }
            ("ignore", AttrArgs::Empty) => FluxAttrKind::Ignore,
            ("opaque", AttrArgs::Empty) => FluxAttrKind::Opaque,
            ("trusted", AttrArgs::Empty) => FluxAttrKind::Trusted,
            ("extern_spec", AttrArgs::Empty) => FluxAttrKind::ExternSpec,
            _ => return Err(self.emit_err(errors::InvalidAttr { span: attr_item.span() })),
        };
        Ok(FluxAttr { kind, span: attr_item.span() })
    }

    // In Prusti they suggested looking into doing this instead of using a Visitor...
    // it seems more brittle but I guess conversely their version is a little permissive.
    fn extract_extern_def_id_from_extern_spec_fn(
        &mut self,
        def_id: LocalDefId,
    ) -> Result<DefId, ErrorGuaranteed> {
        use rustc_hir::{def, ExprKind, Node};
        // Regular functions
        if let Node::Item(i) = self.tcx.hir().find_by_def_id(def_id).unwrap()
            && let ItemKind::Fn(_, _, body_id) = &i.kind
            && let Node::Expr(e) = self.tcx.hir().find(body_id.hir_id).unwrap()
            && let ExprKind::Block(b, _) = e.kind
            && let Some(e) = b.expr
            && let ExprKind::Call(callee, _) = &e.kind
            && let ExprKind::Path(qself) = &callee.kind
        {
                let typeck_result = self.tcx.typeck(def_id);
                if let def::Res::Def(_, def_id) = typeck_result.qpath_res(qself, callee.hir_id)
                {
                    return Ok(def_id);
                }
        }
        // impl functions
        if let Node::ImplItem(i) = self.tcx.hir().find_by_def_id(def_id).unwrap()
            && let ImplItemKind::Fn(_, body_id) = &i.kind
            && let Node::Expr(e) = self.tcx.hir().find(body_id.hir_id).unwrap()
            && let ExprKind::Block(b, _) = e.kind
            && let Some(e) = b.expr
            && let ExprKind::Call(callee, _) = &e.kind
            && let ExprKind::Path(qself) = &callee.kind
        {
                let typeck_result = self.tcx.typeck(def_id);
                if let def::Res::Def(_, def_id) = typeck_result.qpath_res(qself, callee.hir_id)
                {
                    return Ok(def_id);
                }
        }
        Err(self.emit_err(errors::MalformedExternSpec { span: self.tcx.def_span(def_id) }))
    }

    fn extract_extern_def_id_from_extern_spec_struct(
        &mut self,
        def_id: LocalDefId,
        data: &VariantData,
    ) -> Result<DefId, ErrorGuaranteed> {
        if let Some(extern_field) = data.fields().first() {
            let ty = self.tcx.type_of(extern_field.def_id);
            if let Some(adt_def) = ty.skip_binder().ty_adt_def() {
                return Ok(adt_def.did());
            }
        }
        Err(self.emit_err(errors::MalformedExternSpec { span: self.tcx.def_span(def_id) }))
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
        let mut err = None;
        for (name, dups) in attrs.dups() {
            for attr in dups {
                if attr.allow_dups() {
                    continue;
                }
                err = Some(self.emit_err(errors::DuplicatedAttr { span: attr.span, name }));
            }
        }
        if let Some(e) = err {
            self.error_guaranteed = Some(e);
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
            fn_sigs: FxHashMap::default(),
            structs: FxHashMap::default(),
            enums: FxHashMap::default(),
            qualifs: Vec::default(),
            sort_decls: Vec::default(),
            func_defs: Vec::default(),
            aliases: FxHashMap::default(),
            ignores: FxHashSet::default(),
            consts: FxHashMap::default(),
            crate_config: None,
            extern_specs: FxHashMap::default(),
        }
    }

    fn extend_items(&mut self, items: impl IntoIterator<Item = surface::Item>) {
        for item in items {
            match item {
                surface::Item::Qualifier(qualifier) => self.qualifs.push(qualifier),
                surface::Item::FuncDef(defn) => self.func_defs.push(defn),
                surface::Item::SortDecl(sort_decl) => self.sort_decls.push(sort_decl),
            }
        }
    }

    pub fn refined_bys(&self) -> impl Iterator<Item = (OwnerId, Option<&surface::RefinedBy>)> {
        let structs = self
            .structs
            .iter()
            .map(|(owner_id, struct_def)| (*owner_id, struct_def.refined_by.as_ref()));
        let enums = self
            .enums
            .iter()
            .map(|(owner_id, enum_def)| (*owner_id, enum_def.refined_by.as_ref()));
        let aliases = self
            .aliases
            .iter()
            .map(|(owner_id, alias)| (*owner_id, alias.as_ref().map(|alias| &alias.refined_by)));
        itertools::chain!(structs, enums, aliases)
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
    Trusted,
    Opaque,
    FnSig(surface::FnSig),
    RefinedBy(surface::RefinedBy),
    QualNames(surface::QualNames),
    Items(Vec<surface::Item>),
    TypeAlias(surface::TyAlias),
    Field(surface::Ty),
    Variant(surface::VariantDef),
    ConstSig(surface::ConstSig),
    CrateConfig(config::CrateConfig),
    Invariant(surface::Expr),
    Ignore,
    ExternSpec,
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

    fn trusted(&mut self) -> bool {
        read_flag!(self, Trusted)
    }

    fn ignore(&mut self) -> bool {
        read_flag!(self, Ignore)
    }

    fn opaque(&mut self) -> bool {
        read_flag!(self, Opaque)
    }

    fn items(&mut self) -> impl Iterator<Item = surface::Item> {
        read_attrs!(self, Items).into_iter().flatten()
    }

    fn fn_sig(&mut self) -> Option<surface::FnSig> {
        read_attr!(self, FnSig)
    }

    fn const_sig(&mut self) -> Option<surface::ConstSig> {
        read_attr!(self, ConstSig)
    }

    fn qual_names(&mut self) -> Option<surface::QualNames> {
        read_attr!(self, QualNames)
    }

    fn alias(&mut self) -> Option<surface::TyAlias> {
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

    fn extern_spec(&mut self) -> bool {
        read_flag!(self, ExternSpec)
    }

    fn contains(&self, attr: &str) -> Option<Span> {
        self.map.get(attr).and_then(|attrs| {
            match &attrs[..] {
                [attr] => Some(attr.span),
                _ => None,
            }
        })
    }
}

impl FluxAttrKind {
    fn name(&self) -> &'static str {
        match self {
            FluxAttrKind::Trusted => attr_name!(Trusted),
            FluxAttrKind::Opaque => attr_name!(Opaque),
            FluxAttrKind::FnSig(_) => attr_name!(FnSig),
            FluxAttrKind::ConstSig(_) => attr_name!(ConstSig),
            FluxAttrKind::RefinedBy(_) => attr_name!(RefinedBy),
            FluxAttrKind::Items(_) => attr_name!(Items),
            FluxAttrKind::QualNames(_) => attr_name!(QualNames),
            FluxAttrKind::Field(_) => attr_name!(Field),
            FluxAttrKind::Variant(_) => attr_name!(Variant),
            FluxAttrKind::TypeAlias(_) => attr_name!(TypeAlias),
            FluxAttrKind::CrateConfig(_) => attr_name!(CrateConfig),
            FluxAttrKind::Ignore => attr_name!(Ignore),
            FluxAttrKind::Invariant(_) => attr_name!(Invariant),
            FluxAttrKind::ExternSpec => attr_name!(ExternSpec),
        }
    }
}

#[derive(Debug)]
struct CFGSetting {
    setting: Symbol,
    span: Span,
}

#[derive(Debug)]
struct FluxAttrCFG {
    map: HashMap<String, CFGSetting>,
}

macro_rules! try_read_setting {
    ($self:expr, $setting:ident, $type:ident, $cfg:expr) => {
        if let Some(CFGSetting { setting, span }) = $self.map.remove(stringify!($setting)) {
            let parse_result = setting.as_str().parse::<$type>();
            if let Ok(val) = parse_result {
                $cfg.$setting = val;
            } else {
                return Err(errors::CFGError {
                    span,
                    message: format!(
                        "incorrect type in value for setting `{}`, expected {}",
                        stringify!($setting),
                        stringify!($type)
                    ),
                });
            }
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
                    let value = item.name_value_literal().ok_or_else(|| {
                        errors::CFGError { span, message: "unsupported value".to_string() }
                    })?;

                    let setting = CFGSetting { setting: value.symbol, span: item.span };
                    self.map.insert(name, setting);
                    return Ok(());
                }
                Err(errors::CFGError { span, message: "bad setting name".to_string() })
            }
            NestedMetaItem::Lit(_) => {
                Err(errors::CFGError {
                    span: nested_item.span(),
                    message: "unsupported item".to_string(),
                })
            }
        }
    }

    fn try_into_crate_cfg(&mut self) -> Result<config::CrateConfig, errors::CFGError> {
        let mut crate_config = CrateConfig::default();
        try_read_setting!(self, check_overflow, bool, crate_config);
        try_read_setting!(self, scrape_quals, bool, crate_config);

        if let Some((name, setting)) = self.map.iter().next() {
            return Err(errors::CFGError {
                span: setting.span,
                message: format!("invalid crate cfg keyword `{name}`"),
            });
        }

        Ok(crate_config)
    }
}

mod errors {
    use flux_macros::Diagnostic;
    use rustc_span::Span;

    #[derive(Diagnostic)]
    #[diag(driver_duplicated_attr, code = "FLUX")]
    pub struct DuplicatedAttr {
        #[primary_span]
        pub span: Span,
        pub name: &'static str,
    }

    #[derive(Diagnostic)]
    #[diag(driver_invalid_attr, code = "FLUX")]
    pub struct InvalidAttr {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(driver_invalid_constant, code = "FLUX")]
    pub struct InvalidConstant {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(driver_cfg_error, code = "FLUX")]
    pub struct CFGError {
        #[primary_span]
        pub span: Span,
        pub message: String,
    }

    #[derive(Diagnostic)]
    #[diag(driver_syntax_err, code = "FLUX")]
    pub struct SyntaxErr {
        #[primary_span]
        pub span: Span,
        pub msg: &'static str,
    }

    #[derive(Diagnostic)]
    #[diag(driver_malformed_extern_spec, code = "FLUX")]
    pub struct MalformedExternSpec {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(driver_missing_fn_sig_for_extern_spec, code = "FLUX")]
    pub struct MissingFnSigForExternSpec {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(driver_attr_on_opaque, code = "FLUX")]
    pub(super) struct AttrOnOpaque {
        #[primary_span]
        span: Span,
        #[label]
        field_span: Span,
    }

    impl AttrOnOpaque {
        pub(super) fn new(span: Span, field: &rustc_hir::FieldDef) -> Self {
            let field_span = field.ident.span;
            Self { span, field_span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(driver_missing_variant, code = "FLUX")]
    #[note]
    pub(super) struct MissingVariant {
        #[primary_span]
        #[label]
        span: Span,
    }

    impl MissingVariant {
        pub(super) fn new(span: Span) -> Self {
            Self { span }
        }
    }

    impl From<flux_syntax::ParseError> for SyntaxErr {
        fn from(err: flux_syntax::ParseError) -> Self {
            use flux_syntax::ParseErrorKind;
            let msg = match err.kind {
                ParseErrorKind::UnexpectedEof => "type annotation ended unexpectedly",
                ParseErrorKind::UnexpectedToken => "unexpected token",
                ParseErrorKind::IntTooLarge => "integer literal is too large",
            };

            SyntaxErr { span: err.span, msg }
        }
    }
}
