mod annot_stats;
mod extern_specs;

use std::collections::HashMap;

use annot_stats::Stats;
use extern_specs::ExternSpecCollector;
use flux_common::{
    iter::IterExt,
    result::{ErrorCollector, ResultExt},
    tracked_span_assert_eq,
};
use flux_config::{self as config, PartialInferOpts, SmtSolver};
use flux_errors::{Errors, FluxSession};
use flux_middle::{
    Specs,
    fhir::{Ignored, Trusted},
};
use flux_syntax::{ParseResult, ParseSess, surface};
use itertools::Itertools;
use rustc_ast::{MetaItemInner, MetaItemKind, tokenstream::TokenStream};
use rustc_errors::ErrorGuaranteed;
use rustc_hir::{
    self as hir, Attribute, CRATE_OWNER_ID, EnumDef, ImplItemKind, Item, ItemKind, OwnerId,
    VariantData,
    def::DefKind,
    def_id::{CRATE_DEF_ID, LocalDefId},
};
use rustc_middle::ty::TyCtxt;
use rustc_span::{Span, Symbol, SyntaxContext};

use crate::collector::{hir::def_id::LocalModDefId, surface::Ident};
type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

pub(crate) struct SpecCollector<'sess, 'tcx> {
    tcx: TyCtxt<'tcx>,
    parse_sess: ParseSess,
    specs: Specs,
    errors: Errors<'sess>,
    stats: Stats,
}

macro_rules! attr_name {
    ($kind:ident) => {{
        let _ = FluxAttrKind::$kind;
        stringify!($kind)
    }};
}

impl<'tcx> hir::intravisit::Visitor<'tcx> for SpecCollector<'_, 'tcx> {
    type NestedFilter = rustc_middle::hir::nested_filter::All;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_item(&mut self, item: &'tcx Item<'tcx>) {
        let _ = self.collect_item(item);
    }

    fn visit_trait_item(&mut self, trait_item: &'tcx rustc_hir::TraitItem<'tcx>) {
        let _ = self.collect_trait_item(trait_item);
    }

    fn visit_impl_item(&mut self, impl_item: &'tcx rustc_hir::ImplItem<'tcx>) {
        let _ = self.collect_impl_item(impl_item);
    }
}

impl<'a, 'tcx> SpecCollector<'a, 'tcx> {
    pub(crate) fn collect(tcx: TyCtxt<'tcx>, sess: &'a FluxSession) -> Result<Specs> {
        let mut collector = Self {
            tcx,
            parse_sess: ParseSess::default(),
            specs: Specs::default(),
            errors: Errors::new(sess),
            stats: Default::default(),
        };

        let _ = collector.collect_crate();
        tcx.hir_walk_toplevel_module(&mut collector);

        if config::annots() {
            collector.stats.save(tcx).unwrap();
        }

        collector.errors.into_result()?;

        Ok(collector.specs)
    }

    fn collect_crate(&mut self) -> Result {
        let mut attrs = self.parse_attrs_and_report_dups(CRATE_DEF_ID)?;
        self.collect_ignore_and_trusted(&mut attrs, CRATE_DEF_ID);
        self.collect_infer_opts(&mut attrs, CRATE_DEF_ID);
        self.collect_detached_specs(&mut attrs, CRATE_DEF_ID)?;
        self.specs
            .flux_items_by_parent
            .entry(CRATE_OWNER_ID)
            .or_default()
            .extend(attrs.items());
        Ok(())
    }

    fn collect_item(&mut self, item: &'tcx Item<'tcx>) -> Result {
        let owner_id = item.owner_id;

        let mut attrs = self.parse_attrs_and_report_dups(owner_id.def_id)?;
        self.collect_ignore_and_trusted(&mut attrs, owner_id.def_id);
        self.collect_infer_opts(&mut attrs, owner_id.def_id);

        match &item.kind {
            ItemKind::Fn { .. } => {
                self.collect_fn_spec(owner_id, attrs)?;
            }
            ItemKind::Struct(_, _, variant) => {
                self.collect_struct_def(owner_id, attrs, variant)?;
            }
            ItemKind::Union(_, _, variant) => {
                // currently no refinements on unions
                tracked_span_assert_eq!(attrs.items().is_empty(), true);
                self.collect_struct_def(owner_id, attrs, variant)?;
            }
            ItemKind::Enum(_, _, enum_def) => {
                self.collect_enum_def(owner_id, attrs, enum_def)?;
            }
            ItemKind::Mod(..) => self.collect_mod(owner_id, attrs)?,
            ItemKind::TyAlias(..) => self.collect_type_alias(owner_id, attrs)?,
            ItemKind::Impl(..) => self.collect_impl(owner_id, attrs)?,
            ItemKind::Trait(..) => self.collect_trait(owner_id, attrs)?,
            ItemKind::Const(.., body_id) => {
                // The flux-rs macro puts defs as an outer attribute on a `const _: () = { }`. We
                // consider these defs to be defined in the parent of the const.
                self.specs
                    .flux_items_by_parent
                    .entry(self.tcx.hir_get_parent_item(item.hir_id()))
                    .or_default()
                    .extend(attrs.items());

                if attrs.extern_spec() {
                    return ExternSpecCollector::collect(self, *body_id);
                }

                self.collect_constant(owner_id, attrs)?;
            }
            _ => {}
        }
        hir::intravisit::walk_item(self, item);
        Ok(())
    }

    fn collect_trait_item(&mut self, trait_item: &'tcx rustc_hir::TraitItem<'tcx>) -> Result {
        let owner_id = trait_item.owner_id;

        let mut attrs = self.parse_attrs_and_report_dups(owner_id.def_id)?;
        self.collect_ignore_and_trusted(&mut attrs, owner_id.def_id);
        self.collect_infer_opts(&mut attrs, owner_id.def_id);
        if let rustc_hir::TraitItemKind::Fn(_, _) = trait_item.kind {
            self.collect_fn_spec(owner_id, attrs)?;
        }
        hir::intravisit::walk_trait_item(self, trait_item);
        Ok(())
    }

    fn collect_impl_item(&mut self, impl_item: &'tcx rustc_hir::ImplItem<'tcx>) -> Result {
        let owner_id = impl_item.owner_id;

        let mut attrs = self.parse_attrs_and_report_dups(owner_id.def_id)?;
        self.collect_ignore_and_trusted(&mut attrs, owner_id.def_id);
        self.collect_infer_opts(&mut attrs, owner_id.def_id);

        if let ImplItemKind::Fn(..) = &impl_item.kind {
            self.collect_fn_spec(owner_id, attrs)?;
        }
        hir::intravisit::walk_impl_item(self, impl_item);
        Ok(())
    }

    fn collect_mod(&mut self, module_id: OwnerId, mut attrs: FluxAttrs) -> Result {
        self.specs
            .flux_items_by_parent
            .entry(module_id)
            .or_default()
            .extend(attrs.items());
        Ok(())
    }

    fn collect_trait(&mut self, owner_id: OwnerId, mut attrs: FluxAttrs) -> Result {
        let generics = attrs.generics();
        let assoc_refinements = attrs.trait_assoc_refts();

        self.specs
            .traits
            .insert(owner_id, surface::Trait { generics, assoc_refinements });

        Ok(())
    }

    fn collect_impl(&mut self, owner_id: OwnerId, mut attrs: FluxAttrs) -> Result {
        let generics = attrs.generics();
        let assoc_refinements = attrs.impl_assoc_refts();

        self.specs
            .impls
            .insert(owner_id, surface::Impl { generics, assoc_refinements });

        Ok(())
    }

    fn collect_type_alias(&mut self, owner_id: OwnerId, mut attrs: FluxAttrs) -> Result {
        self.specs
            .ty_aliases
            .insert(owner_id, attrs.ty_alias().map(|z| *z));
        Ok(())
    }

    fn collect_struct_def(
        &mut self,
        owner_id: OwnerId,
        mut attrs: FluxAttrs,
        data: &VariantData,
    ) -> Result<&mut surface::StructDef> {
        let opaque = attrs.opaque();
        let refined_by = attrs.refined_by();
        let generics = attrs.generics();

        let fields = data
            .fields()
            .iter()
            .take(data.fields().len())
            .map(|field| self.parse_field_spec(field, opaque))
            .try_collect_exhaust()?;

        let invariants = attrs.invariants();

        Ok(self
            .specs
            .structs
            .entry(owner_id)
            .or_insert(surface::StructDef { generics, refined_by, fields, opaque, invariants }))
    }

    fn parse_constant_spec(&mut self, owner_id: OwnerId, mut attrs: FluxAttrs) -> Result {
        if let Some(constant) = attrs.constant() {
            self.specs.constants.insert(owner_id, constant);
        }
        Ok(())
    }

    fn parse_field_spec(
        &mut self,
        field: &rustc_hir::FieldDef,
        opaque: bool,
    ) -> Result<Option<surface::Ty>> {
        let mut attrs = self.parse_attrs_and_report_dups(field.def_id)?;
        let field_attr = attrs.field();

        // We warn if a struct marked as opaque has a refined type annotation. We allow unrefined
        // annotations, because the `flux!` macro unconditionally adds a `#[flux_tool::field(..)]`
        // annotation, even if the struct is opaque.
        if opaque
            && let Some(ty) = field_attr.as_ref()
            && ty.is_refined()
        {
            return Err(self.errors.emit(errors::AttrOnOpaque::new(ty.span, field)));
        }
        Ok(field_attr)
    }

    fn collect_enum_def(
        &mut self,
        owner_id: OwnerId,
        mut attrs: FluxAttrs,
        enum_def: &EnumDef,
    ) -> Result<&mut surface::EnumDef> {
        let generics = attrs.generics();
        let refined_by = attrs.refined_by();
        let reflected = attrs.reflected();

        if refined_by.is_some() && reflected {
            let span = self.tcx.def_span(owner_id.to_def_id());
            return Err(self
                .errors
                .emit(errors::ReflectedEnumWithRefinedBy::new(span)));
        }

        let variants = enum_def
            .variants
            .iter()
            .take(enum_def.variants.len())
            .map(|variant| self.collect_variant(variant, refined_by.is_some()))
            .try_collect_exhaust()?;

        let invariants = attrs.invariants();

        Ok(self
            .specs
            .enums
            .entry(owner_id)
            .or_insert(surface::EnumDef { generics, refined_by, variants, invariants, reflected }))
    }

    fn collect_variant(
        &mut self,
        hir_variant: &rustc_hir::Variant,
        has_refined_by: bool,
    ) -> Result<Option<surface::VariantDef>> {
        let mut attrs = self.parse_attrs_and_report_dups(hir_variant.def_id)?;

        let variant = attrs.variant();

        if variant.is_none() && has_refined_by {
            return Err(self
                .errors
                .emit(errors::MissingVariant::new(hir_variant.span)));
        }

        Ok(variant)
    }

    fn collect_constant(&mut self, owner_id: OwnerId, attrs: FluxAttrs) -> Result {
        self.parse_constant_spec(owner_id, attrs)
    }

    fn collect_fn_spec(
        &mut self,
        owner_id: OwnerId,
        mut attrs: FluxAttrs,
    ) -> Result<&mut surface::FnSpec> {
        let fn_sig = attrs.fn_sig();

        if let Some(fn_sig) = &fn_sig
            && let Some(ident) = fn_sig.ident
            && let Some(item_ident) = self.tcx.opt_item_ident(owner_id.to_def_id())
            && ident != item_ident
        {
            return Err(self.errors.emit(errors::MismatchedSpecName::new(
                self.tcx,
                ident,
                owner_id.to_def_id(),
            )));
        };

        if attrs.should_fail() {
            self.specs.should_fail.insert(owner_id.def_id);
        }

        let qual_names: Option<surface::QualNames> = attrs.qual_names();

        let reveal_names: Option<surface::RevealNames> = attrs.reveal_names();

        Ok(self
            .specs
            .fn_sigs
            .entry(owner_id)
            .or_insert(surface::FnSpec { fn_sig, qual_names, reveal_names }))
    }

    fn parse_attrs_and_report_dups(&mut self, def_id: LocalDefId) -> Result<FluxAttrs> {
        let attrs = self.parse_flux_attrs(def_id)?;
        self.report_dups(&attrs)?;
        Ok(attrs)
    }

    fn parse_flux_attrs(&mut self, def_id: LocalDefId) -> Result<FluxAttrs> {
        let def_kind = self.tcx.def_kind(def_id);
        let hir_id = self.tcx.local_def_id_to_hir_id(def_id);
        let attrs = self.tcx.hir_attrs(hir_id);
        let attrs: Vec<_> = attrs
            .iter()
            .filter_map(|attr| {
                if let Attribute::Unparsed(attr_item) = &attr {
                    match &attr_item.path.segments[..] {
                        [first, ..] => {
                            let ident = first.as_str();
                            if ident == "flux" || ident == "flux_tool" {
                                Some(attr_item)
                            } else {
                                None
                            }
                        }
                        _ => None,
                    }
                } else {
                    None
                }
            })
            .map(|attr_item| self.parse_flux_attr(attr_item, def_kind))
            .try_collect_exhaust()?;

        Ok(FluxAttrs::new(attrs))
    }

    fn parse_flux_attr(
        &mut self,
        attr_item: &hir::AttrItem,
        def_kind: DefKind,
    ) -> Result<FluxAttr> {
        let invalid_attr_err = |this: &Self| {
            this.errors
                .emit(errors::InvalidAttr { span: attr_item_span(attr_item) })
        };

        let [_, segment] = &attr_item.path.segments[..] else { return Err(invalid_attr_err(self)) };

        let kind = match (segment.as_str(), &attr_item.args) {
            ("alias", hir::AttrArgs::Delimited(dargs)) => {
                self.parse(dargs, ParseSess::parse_type_alias, |t| {
                    FluxAttrKind::TypeAlias(Box::new(t))
                })?
            }
            ("sig" | "spec", hir::AttrArgs::Delimited(dargs)) => {
                self.parse(dargs, ParseSess::parse_fn_sig, FluxAttrKind::FnSig)?
            }
            ("assoc" | "reft", hir::AttrArgs::Delimited(dargs)) => {
                match def_kind {
                    DefKind::Trait => {
                        self.parse(
                            dargs,
                            ParseSess::parse_trait_assoc_reft,
                            FluxAttrKind::TraitAssocReft,
                        )?
                    }
                    DefKind::Impl { .. } => {
                        self.parse(
                            dargs,
                            ParseSess::parse_impl_assoc_reft,
                            FluxAttrKind::ImplAssocReft,
                        )?
                    }
                    _ => return Err(invalid_attr_err(self)),
                }
            }
            ("qualifiers", hir::AttrArgs::Delimited(dargs)) => {
                self.parse(dargs, ParseSess::parse_qual_names, FluxAttrKind::QualNames)?
            }
            ("reveal", hir::AttrArgs::Delimited(dargs)) => {
                self.parse(dargs, ParseSess::parse_reveal_names, FluxAttrKind::RevealNames)?
            }
            ("defs", hir::AttrArgs::Delimited(dargs)) => {
                self.parse(dargs, ParseSess::parse_flux_item, FluxAttrKind::Items)?
            }
            ("refined_by", hir::AttrArgs::Delimited(dargs)) => {
                self.parse(dargs, ParseSess::parse_refined_by, FluxAttrKind::RefinedBy)?
            }
            ("field", hir::AttrArgs::Delimited(dargs)) => {
                self.parse(dargs, ParseSess::parse_type, FluxAttrKind::Field)?
            }
            ("variant", hir::AttrArgs::Delimited(dargs)) => {
                self.parse(dargs, ParseSess::parse_variant, FluxAttrKind::Variant)?
            }
            ("invariant", hir::AttrArgs::Delimited(dargs)) => {
                self.parse(dargs, ParseSess::parse_expr, FluxAttrKind::Invariant)?
            }
            ("constant", hir::AttrArgs::Delimited(dargs)) => {
                self.parse(dargs, ParseSess::parse_constant_info, FluxAttrKind::Constant)?
            }
            ("opts", hir::AttrArgs::Delimited(..)) => {
                let opts = AttrMap::parse(attr_item)
                    .emit(&self.errors)?
                    .try_into_infer_opts()
                    .emit(&self.errors)?;
                FluxAttrKind::InferOpts(opts)
            }
            ("ignore", hir::AttrArgs::Delimited(dargs)) => {
                self.parse(dargs, ParseSess::parse_yes_or_no_with_reason, |b| {
                    FluxAttrKind::Ignore(b.into())
                })?
            }
            ("ignore", hir::AttrArgs::Empty) => FluxAttrKind::Ignore(Ignored::Yes),
            ("trusted", hir::AttrArgs::Delimited(dargs)) => {
                self.parse(dargs, ParseSess::parse_yes_or_no_with_reason, |b| {
                    FluxAttrKind::Trusted(b.into())
                })?
            }
            ("trusted", hir::AttrArgs::Empty) => FluxAttrKind::Trusted(Trusted::Yes),
            ("trusted_impl", hir::AttrArgs::Delimited(dargs)) => {
                self.parse(dargs, ParseSess::parse_yes_or_no_with_reason, |b| {
                    FluxAttrKind::TrustedImpl(b.into())
                })?
            }
            ("trusted_impl", hir::AttrArgs::Empty) => FluxAttrKind::TrustedImpl(Trusted::Yes),
            ("opaque", hir::AttrArgs::Empty) => FluxAttrKind::Opaque,
            ("reflect", hir::AttrArgs::Empty) => FluxAttrKind::Reflect,
            ("extern_spec", hir::AttrArgs::Empty) => FluxAttrKind::ExternSpec,
            ("should_fail", hir::AttrArgs::Empty) => FluxAttrKind::ShouldFail,
            ("specs", hir::AttrArgs::Delimited(dargs)) => {
                self.parse(dargs, ParseSess::parse_detached_specs, FluxAttrKind::DetachedSpecs)?
            }
            _ => return Err(invalid_attr_err(self)),
        };
        if config::annots() {
            self.stats.add(self.tcx, segment.as_str(), &attr_item.args);
        }
        Ok(FluxAttr { kind, span: attr_item_span(attr_item) })
    }

    fn parse<T>(
        &mut self,
        dargs: &rustc_ast::DelimArgs,
        parser: impl FnOnce(&mut ParseSess, &TokenStream, Span) -> ParseResult<T>,
        ctor: impl FnOnce(T) -> FluxAttrKind,
    ) -> Result<FluxAttrKind> {
        let entire = dargs.dspan.entire().with_ctxt(SyntaxContext::root());
        parser(&mut self.parse_sess, &dargs.tokens, entire)
            .map(ctor)
            .map_err(errors::SyntaxErr::from)
            .emit(&self.errors)
    }

    fn report_dups(&mut self, attrs: &FluxAttrs) -> Result {
        let mut err = None;
        for (name, dups) in attrs.dups() {
            for attr in dups {
                if attr.allow_dups() {
                    continue;
                }
                err.collect(
                    self.errors
                        .emit(errors::DuplicatedAttr { span: attr.span, name }),
                );
            }
        }
        err.into_result()
    }

    fn collect_ignore_and_trusted(&mut self, attrs: &mut FluxAttrs, def_id: LocalDefId) {
        if let Some(ignored) = attrs.ignore() {
            self.specs.ignores.insert(def_id, ignored);
        }
        if let Some(trusted) = attrs.trusted() {
            self.specs.trusted.insert(def_id, trusted);
        }
        if let Some(trusted_impl) = attrs.trusted_impl() {
            self.specs.trusted_impl.insert(def_id, trusted_impl);
        }
    }

    fn collect_infer_opts(&mut self, attrs: &mut FluxAttrs, def_id: LocalDefId) {
        if let Some(infer_opts) = attrs.infer_opts() {
            self.specs.infer_opts.insert(def_id, infer_opts);
        }
    }

    fn collect_detached_specs(&mut self, attrs: &mut FluxAttrs, def_id: LocalDefId) -> Result {
        let Some(detached_specs) = attrs.detached_specs() else {
            return Ok(());
        };

        self.collect_detached_specs_visitor(detached_specs, def_id)
    }

    fn collect_detached_specs_visitor(
        &mut self,
        detached_specs: surface::DetachedSpecs,
        parent: LocalDefId,
    ) -> Result {
        let mut idents = detached_specs
            .items
            .into_iter()
            .map(|item| (item.ident(), (item, None)))
            .collect();

        resolve_idents_in_scope(self.tcx, parent, &mut idents);

        for (ident, (item, def_id)) in idents {
            let Some(def_id) = def_id else {
                return Err(self.errors.emit(errors::AttrMapErr {
                    span: ident.span,
                    message: format!("unresolved identifier `{ident}`"),
                }));
            };
            let owner_id = self.tcx.local_def_id_to_hir_id(def_id).owner;
            self.collect_detached_item(owner_id, item)?;
        }
        Ok(())
    }

    fn collect_detached_item(&mut self, owner_id: OwnerId, item: surface::DetachedItem) -> Result {
        match item {
            surface::DetachedItem::FnSig(_, fn_sig) => {
                self.specs
                    .fn_sigs
                    .entry(owner_id)
                    .or_insert(surface::FnSpec {
                        fn_sig: Some(*fn_sig),
                        qual_names: None,
                        reveal_names: None,
                    });
                Ok(())
            }
            surface::DetachedItem::Mod(_, detached_specs) => {
                self.collect_detached_specs_visitor(detached_specs, owner_id.def_id)
            }
        }
    }
}

struct DetachedIdentResolver<'a> {
    items: &'a mut HashMap<Ident, (surface::DetachedItem, Option<LocalDefId>)>,
}

impl<'tcx> hir::intravisit::Visitor<'tcx> for DetachedIdentResolver<'_> {
    fn visit_item(&mut self, item: &'tcx Item<'tcx>) {
        if let ItemKind::Fn { ident, .. } = item.kind
            && let Some(val) = self.items.get_mut(&ident)
            && matches!(val.0, surface::DetachedItem::FnSig(_, _))
            && val.1.is_none()
        {
            val.1 = Some(item.owner_id.def_id);
        }
        if let ItemKind::Mod(ident, ..) = item.kind
            && let Some(val) = self.items.get_mut(&ident)
            && matches!(val.0, surface::DetachedItem::Mod(_, _))
            && val.1.is_none()
        {
            val.1 = Some(item.owner_id.def_id);
        }
    }
}

fn resolve_idents_in_scope(
    tcx: TyCtxt,
    scope: LocalDefId,
    items: &mut HashMap<Ident, (surface::DetachedItem, Option<LocalDefId>)>,
) {
    let scope = LocalModDefId::new_unchecked(scope);
    tcx.hir_visit_item_likes_in_module(scope, &mut DetachedIdentResolver { items });
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
    Trusted(Trusted),
    TrustedImpl(Trusted),
    Opaque,
    Reflect,
    FnSig(surface::FnSig),
    TraitAssocReft(Vec<surface::TraitAssocReft>),
    ImplAssocReft(Vec<surface::ImplAssocReft>),
    RefinedBy(surface::RefineParams),
    Generics(surface::Generics),
    QualNames(surface::QualNames),
    RevealNames(surface::RevealNames),
    Items(Vec<surface::Item>),
    TypeAlias(Box<surface::TyAlias>),
    Field(surface::Ty),
    Constant(surface::ConstantInfo),
    Variant(surface::VariantDef),
    InferOpts(config::PartialInferOpts),
    Invariant(surface::Expr),
    Ignore(Ignored),
    ShouldFail,
    ExternSpec,
    /// See `detachXX.rs`
    DetachedSpecs(surface::DetachedSpecs),
}

macro_rules! read_flag {
    ($self:expr, $kind:ident) => {{ $self.map.get(attr_name!($kind)).is_some() }};
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
        matches!(
            &self.kind,
            FluxAttrKind::Invariant(..)
                | FluxAttrKind::TraitAssocReft(..)
                | FluxAttrKind::ImplAssocReft(..)
        )
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

    fn trusted(&mut self) -> Option<Trusted> {
        read_attr!(self, Trusted)
    }

    fn trusted_impl(&mut self) -> Option<Trusted> {
        read_attr!(self, TrustedImpl)
    }

    fn ignore(&mut self) -> Option<Ignored> {
        read_attr!(self, Ignore)
    }

    fn opaque(&self) -> bool {
        read_flag!(self, Opaque)
    }

    fn reflected(&self) -> bool {
        read_flag!(self, Reflect)
    }

    fn items(&mut self) -> Vec<surface::Item> {
        read_attrs!(self, Items).into_iter().flatten().collect()
    }

    fn fn_sig(&mut self) -> Option<surface::FnSig> {
        read_attr!(self, FnSig)
    }

    fn qual_names(&mut self) -> Option<surface::QualNames> {
        read_attr!(self, QualNames)
    }

    fn reveal_names(&mut self) -> Option<surface::RevealNames> {
        read_attr!(self, RevealNames)
    }

    fn ty_alias(&mut self) -> Option<Box<surface::TyAlias>> {
        read_attr!(self, TypeAlias)
    }

    fn refined_by(&mut self) -> Option<surface::RefineParams> {
        read_attr!(self, RefinedBy)
    }

    fn generics(&mut self) -> Option<surface::Generics> {
        read_attr!(self, Generics)
    }

    fn trait_assoc_refts(&mut self) -> Vec<surface::TraitAssocReft> {
        read_attrs!(self, TraitAssocReft)
            .into_iter()
            .flatten()
            .collect()
    }

    fn impl_assoc_refts(&mut self) -> Vec<surface::ImplAssocReft> {
        read_attrs!(self, ImplAssocReft)
            .into_iter()
            .flatten()
            .collect()
    }

    fn field(&mut self) -> Option<surface::Ty> {
        read_attr!(self, Field)
    }

    fn constant(&mut self) -> Option<surface::ConstantInfo> {
        read_attr!(self, Constant)
    }

    fn variant(&mut self) -> Option<surface::VariantDef> {
        read_attr!(self, Variant)
    }

    fn infer_opts(&mut self) -> Option<config::PartialInferOpts> {
        read_attr!(self, InferOpts)
    }

    fn invariants(&mut self) -> Vec<surface::Expr> {
        read_attrs!(self, Invariant)
    }

    fn extern_spec(&self) -> bool {
        read_flag!(self, ExternSpec)
    }

    fn should_fail(&self) -> bool {
        read_flag!(self, ShouldFail)
    }

    fn detached_specs(&mut self) -> Option<surface::DetachedSpecs> {
        read_attr!(self, DetachedSpecs)
    }
}

impl FluxAttrKind {
    fn name(&self) -> &'static str {
        match self {
            FluxAttrKind::Trusted(_) => attr_name!(Trusted),
            FluxAttrKind::TrustedImpl(_) => attr_name!(TrustedImpl),
            FluxAttrKind::Opaque => attr_name!(Opaque),
            FluxAttrKind::Reflect => attr_name!(Reflect),
            FluxAttrKind::FnSig(_) => attr_name!(FnSig),
            FluxAttrKind::TraitAssocReft(_) => attr_name!(TraitAssocReft),
            FluxAttrKind::ImplAssocReft(_) => attr_name!(ImplAssocReft),
            FluxAttrKind::RefinedBy(_) => attr_name!(RefinedBy),
            FluxAttrKind::Generics(_) => attr_name!(Generics),
            FluxAttrKind::Items(_) => attr_name!(Items),
            FluxAttrKind::QualNames(_) => attr_name!(QualNames),
            FluxAttrKind::RevealNames(_) => attr_name!(RevealNames),
            FluxAttrKind::Field(_) => attr_name!(Field),
            FluxAttrKind::Constant(_) => attr_name!(Constant),
            FluxAttrKind::Variant(_) => attr_name!(Variant),
            FluxAttrKind::TypeAlias(_) => attr_name!(TypeAlias),
            FluxAttrKind::InferOpts(_) => attr_name!(InferOpts),
            FluxAttrKind::Ignore(_) => attr_name!(Ignore),
            FluxAttrKind::Invariant(_) => attr_name!(Invariant),
            FluxAttrKind::ShouldFail => attr_name!(ShouldFail),
            FluxAttrKind::ExternSpec => attr_name!(ExternSpec),
            FluxAttrKind::DetachedSpecs(_) => attr_name!(DetachedSpecs),
        }
    }
}

#[derive(Debug)]
struct AttrMapValue {
    setting: Symbol,
    span: Span,
}

#[derive(Debug)]
struct AttrMap {
    map: HashMap<String, AttrMapValue>,
}

macro_rules! try_read_setting {
    ($self:expr, $setting:ident, $type:ident, $cfg:expr) => {{
        let val =
            if let Some(AttrMapValue { setting, span }) = $self.map.remove(stringify!($setting)) {
                let parse_result = setting.as_str().parse::<$type>();
                if let Ok(val) = parse_result {
                    Some(val)
                } else {
                    return Err(errors::AttrMapErr {
                        span,
                        message: format!(
                            "incorrect type in value for setting `{}`, expected {}",
                            stringify!($setting),
                            stringify!($type)
                        ),
                    });
                }
            } else {
                None
            };
        $cfg.$setting = val;
    }};
}

type AttrMapErr<T = ()> = std::result::Result<T, errors::AttrMapErr>;

impl AttrMap {
    fn parse(attr_item: &hir::AttrItem) -> AttrMapErr<Self> {
        let mut map = Self { map: HashMap::new() };
        let err = || {
            Err(errors::AttrMapErr {
                span: attr_item_span(attr_item),
                message: "bad syntax".to_string(),
            })
        };
        let hir::AttrArgs::Delimited(d) = &attr_item.args else { return err() };
        let Some(items) = MetaItemKind::list_from_tokens(d.tokens.clone()) else { return err() };
        for item in items {
            map.parse_entry(&item)?;
        }
        Ok(map)
    }

    fn parse_entry(&mut self, nested_item: &MetaItemInner) -> AttrMapErr {
        match nested_item {
            MetaItemInner::MetaItem(item) => {
                let name = item.name().map(|sym| sym.to_ident_string());
                let span = item.span;
                if let Some(name) = name {
                    if self.map.contains_key(&name) {
                        return Err(errors::AttrMapErr {
                            span,
                            message: format!("duplicated key `{name}`"),
                        });
                    }

                    // TODO: support types of values other than strings
                    let value = item.name_value_literal().ok_or_else(|| {
                        errors::AttrMapErr { span, message: "unsupported value".to_string() }
                    })?;

                    let setting = AttrMapValue { setting: value.symbol, span: item.span };
                    self.map.insert(name, setting);
                    return Ok(());
                }
                Err(errors::AttrMapErr { span, message: "bad setting name".to_string() })
            }
            MetaItemInner::Lit(_) => {
                Err(errors::AttrMapErr {
                    span: nested_item.span(),
                    message: "unsupported item".to_string(),
                })
            }
        }
    }

    fn try_into_infer_opts(&mut self) -> AttrMapErr<PartialInferOpts> {
        let mut infer_opts = PartialInferOpts::default();
        try_read_setting!(self, allow_uninterpreted_cast, bool, infer_opts);
        try_read_setting!(self, check_overflow, bool, infer_opts);
        try_read_setting!(self, scrape_quals, bool, infer_opts);
        try_read_setting!(self, solver, SmtSolver, infer_opts);

        if let Some((name, setting)) = self.map.iter().next() {
            return Err(errors::AttrMapErr {
                span: setting.span,
                message: format!("invalid crate cfg keyword `{name}`"),
            });
        }

        Ok(infer_opts)
    }
}

fn attr_item_span(attr_item: &hir::AttrItem) -> Span {
    attr_args_span(&attr_item.args)
        .map_or(attr_item.path.span, |args_span| attr_item.path.span.to(args_span))
}

fn attr_args_span(attr_args: &hir::AttrArgs) -> Option<Span> {
    match attr_args {
        hir::AttrArgs::Empty => None,
        hir::AttrArgs::Delimited(args) => Some(args.dspan.entire()),
        hir::AttrArgs::Eq { eq_span, expr } => Some(eq_span.to(expr.span)),
    }
}

mod errors {
    use flux_errors::E0999;
    use flux_macros::Diagnostic;
    use itertools::Itertools;
    use rustc_errors::{Diag, DiagCtxtHandle, Diagnostic, Level};
    use rustc_hir::def_id::DefId;
    use rustc_middle::ty::TyCtxt;
    use rustc_span::{ErrorGuaranteed, Span, symbol::Ident};

    #[derive(Diagnostic)]
    #[diag(driver_duplicated_attr, code = E0999)]
    pub(super) struct DuplicatedAttr {
        #[primary_span]
        pub span: Span,
        pub name: &'static str,
    }

    #[derive(Diagnostic)]
    #[diag(driver_invalid_attr, code = E0999)]
    pub(super) struct InvalidAttr {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(driver_invalid_attr_map, code = E0999)]
    pub(super) struct AttrMapErr {
        #[primary_span]
        pub span: Span,
        pub message: String,
    }

    pub(super) struct SyntaxErr(flux_syntax::ParseError);

    impl From<flux_syntax::ParseError> for SyntaxErr {
        fn from(err: flux_syntax::ParseError) -> Self {
            SyntaxErr(err)
        }
    }

    impl<'sess> Diagnostic<'sess> for SyntaxErr {
        fn into_diag(
            self,
            dcx: DiagCtxtHandle<'sess>,
            level: Level,
        ) -> Diag<'sess, ErrorGuaranteed> {
            use flux_syntax::ParseErrorKind;
            let mut diag = Diag::new(dcx, level, crate::fluent_generated::driver_syntax_err);
            diag.code(E0999).span(self.0.span).span_label(
                self.0.span,
                match &self.0.kind {
                    ParseErrorKind::UnexpectedEof => "unexpected end of input".to_string(),
                    ParseErrorKind::UnexpectedToken { expected } => {
                        match &expected[..] {
                            [] => "unexpected token".to_string(),
                            [a] => format!("unexpected token, expected `{a}`"),
                            [a, b] => format!("unexpected token, expected `{a}` or `{b}`"),
                            [prefix @ .., last] => {
                                format!(
                                    "unexpected token, expected one of {}, or `{last}`",
                                    prefix
                                        .iter()
                                        .format_with(", ", |it, f| f(&format_args!("`{it}`")))
                                )
                            }
                        }
                    }
                    ParseErrorKind::CannotBeChained => "operator cannot be chained".to_string(),
                    ParseErrorKind::InvalidBinding => {
                        "identifier must be a mutable reference".to_string()
                    }
                    ParseErrorKind::InvalidSort => {
                        "property parameter sort is inherited from the primitive operator"
                            .to_string()
                    }
                    ParseErrorKind::InvalidDetachedSpec => {
                        "detached spec requires an identifier name".to_string()
                    }
                },
            );
            diag
        }
    }

    #[derive(Diagnostic)]
    #[diag(driver_attr_on_opaque, code = E0999)]
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
    #[diag(driver_reflected_enum_with_refined_by, code = E0999)]
    pub(super) struct ReflectedEnumWithRefinedBy {
        #[primary_span]
        #[label]
        span: Span,
    }
    impl ReflectedEnumWithRefinedBy {
        pub(super) fn new(span: Span) -> Self {
            Self { span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(driver_missing_variant, code = E0999)]
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

    #[derive(Diagnostic)]
    #[diag(driver_mismatched_spec_name, code = E0999)]
    pub(super) struct MismatchedSpecName {
        #[primary_span]
        #[label]
        span: Span,
        #[label(driver_item_def_ident)]
        item_ident_span: Span,
        item_ident: Ident,
        def_descr: &'static str,
    }

    impl MismatchedSpecName {
        pub(super) fn new(tcx: TyCtxt, ident: Ident, def_id: DefId) -> Self {
            let def_descr = tcx.def_descr(def_id);
            let item_ident = tcx.opt_item_ident(def_id).unwrap();
            Self { span: ident.span, item_ident_span: item_ident.span, item_ident, def_descr }
        }
    }
}
