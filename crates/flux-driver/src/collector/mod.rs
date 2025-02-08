mod extern_specs;

use std::collections::HashMap;

use extern_specs::ExternSpecCollector;
use flux_common::{
    iter::IterExt,
    result::{ErrorCollector, ResultExt},
    tracked_span_assert_eq,
};
use flux_config::{self as config, PartialInferOpts, SmtSolver};
use flux_errors::{Errors, FluxSession};
use flux_middle::{
    fhir::{Ignored, Trusted},
    Specs,
};
use flux_syntax::{surface, ParseResult, ParseSess};
use itertools::Itertools;
use rustc_ast::{
    tokenstream::TokenStream, AttrArgs, AttrItem, AttrKind, MetaItemInner, MetaItemKind,
};
use rustc_errors::ErrorGuaranteed;
use rustc_hir::{
    self as hir,
    def::DefKind,
    def_id::{LocalDefId, CRATE_DEF_ID},
    EnumDef, ImplItemKind, Item, ItemKind, OwnerId, VariantData, CRATE_OWNER_ID,
};
use rustc_middle::ty::TyCtxt;
use rustc_span::{symbol::sym, Span, Symbol, SyntaxContext};

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

pub(crate) struct SpecCollector<'sess, 'tcx> {
    tcx: TyCtxt<'tcx>,
    parse_sess: ParseSess,
    specs: Specs,
    errors: Errors<'sess>,
}

macro_rules! attr_name {
    ($kind:ident) => {{
        let _ = FluxAttrKind::$kind;
        stringify!($kind)
    }};
}

impl<'tcx> hir::intravisit::Visitor<'tcx> for SpecCollector<'_, 'tcx> {
    type NestedFilter = rustc_middle::hir::nested_filter::All;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.tcx.hir()
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
        };

        let _ = collector.collect_crate();
        tcx.hir().walk_toplevel_module(&mut collector);

        collector.errors.into_result()?;

        Ok(collector.specs)
    }

    fn collect_crate(&mut self) -> Result {
        let mut attrs = self.parse_attrs_and_report_dups(CRATE_DEF_ID)?;
        self.collect_ignore_and_trusted(&mut attrs, CRATE_DEF_ID);
        self.collect_infer_opts(&mut attrs, CRATE_DEF_ID);
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
            ItemKind::Fn(..) => {
                self.collect_fn_spec(owner_id, attrs)?;
            }
            ItemKind::Struct(variant, ..) => {
                self.collect_struct_def(owner_id, attrs, variant)?;
            }
            ItemKind::Union(variant, ..) => {
                // currently no refinements on unions
                tracked_span_assert_eq!(attrs.items().is_empty(), true);
                self.collect_struct_def(owner_id, attrs, variant)?;
            }
            ItemKind::Enum(enum_def, ..) => {
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
                    .entry(self.tcx.hir().get_parent_item(item.hir_id()))
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
        self.specs.ty_aliases.insert(owner_id, attrs.ty_alias());
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
            .or_insert(surface::StructDef {
                generics,
                refined_by,
                fields,
                opaque,
                invariants,
                node_id: self.parse_sess.next_node_id(),
            }))
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
            .or_insert(surface::EnumDef {
                generics,
                refined_by,
                variants,
                invariants,
                reflected,
                node_id: self.parse_sess.next_node_id(),
            }))
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
        Ok(self
            .specs
            .fn_sigs
            .entry(owner_id)
            .or_insert(surface::FnSpec { fn_sig, qual_names }))
    }

    fn parse_attrs_and_report_dups(&mut self, def_id: LocalDefId) -> Result<FluxAttrs> {
        let attrs = self.parse_flux_attrs(def_id)?;
        self.report_dups(&attrs)?;
        Ok(attrs)
    }

    fn parse_flux_attrs(&mut self, def_id: LocalDefId) -> Result<FluxAttrs> {
        let def_kind = self.tcx.def_kind(def_id);
        let hir_id = self.tcx.local_def_id_to_hir_id(def_id);
        let attrs = self.tcx.hir().attrs(hir_id);
        let attrs: Vec<_> = attrs
            .iter()
            .filter_map(|attr| {
                if let AttrKind::Normal(attr_item, ..) = &attr.kind {
                    match &attr_item.item.path.segments[..] {
                        [first, ..] => {
                            let ident = first.ident.as_str();
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
            .map(|attr_item| self.parse_flux_attr(&attr_item.item, def_kind))
            .try_collect_exhaust()?;

        Ok(FluxAttrs::new(attrs))
    }

    fn parse_flux_attr(&mut self, attr_item: &AttrItem, def_kind: DefKind) -> Result<FluxAttr> {
        let invalid_attr_err = |this: &Self| {
            this.errors
                .emit(errors::InvalidAttr { span: attr_item.span() })
        };

        let [_, segment] = &attr_item.path.segments[..] else { return Err(invalid_attr_err(self)) };

        let kind = match (segment.ident.as_str(), &attr_item.args) {
            ("alias", AttrArgs::Delimited(dargs)) => {
                self.parse(dargs, ParseSess::parse_type_alias, FluxAttrKind::TypeAlias)?
            }
            ("sig" | "spec", AttrArgs::Delimited(dargs)) => {
                self.parse(dargs, ParseSess::parse_fn_sig, FluxAttrKind::FnSig)?
            }
            ("assoc", AttrArgs::Delimited(dargs)) => {
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
            ("qualifiers", AttrArgs::Delimited(dargs)) => {
                self.parse(dargs, ParseSess::parse_qual_names, FluxAttrKind::QualNames)?
            }
            ("defs", AttrArgs::Delimited(dargs)) => {
                self.parse(dargs, ParseSess::parse_flux_item, FluxAttrKind::Items)?
            }
            ("refined_by", AttrArgs::Delimited(dargs)) => {
                self.parse(dargs, ParseSess::parse_refined_by, FluxAttrKind::RefinedBy)?
            }
            ("generics", AttrArgs::Delimited(dargs)) => {
                self.parse(dargs, ParseSess::parse_generics, FluxAttrKind::Generics)?
            }
            ("field", AttrArgs::Delimited(dargs)) => {
                self.parse(dargs, ParseSess::parse_type, FluxAttrKind::Field)?
            }
            ("variant", AttrArgs::Delimited(dargs)) => {
                self.parse(dargs, ParseSess::parse_variant, FluxAttrKind::Variant)?
            }
            ("invariant", AttrArgs::Delimited(dargs)) => {
                self.parse(dargs, ParseSess::parse_expr, FluxAttrKind::Invariant)?
            }
            ("constant", AttrArgs::Delimited(dargs)) => {
                self.parse(dargs, ParseSess::parse_constant_info, FluxAttrKind::Constant)?
            }
            ("opts", AttrArgs::Delimited(..)) => {
                let opts = AttrMap::parse(attr_item)
                    .emit(&self.errors)?
                    .try_into_infer_opts()
                    .emit(&self.errors)?;
                FluxAttrKind::InferOpts(opts)
            }
            ("ignore", _) => {
                FluxAttrKind::Ignore(
                    parse_yes_no_with_reason(attr_item)
                        .map_err(|_| invalid_attr_err(self))?
                        .into(),
                )
            }
            ("trusted", _) => {
                FluxAttrKind::Trusted(
                    parse_yes_no_with_reason(attr_item)
                        .map_err(|_| invalid_attr_err(self))?
                        .into(),
                )
            }
            ("trusted_impl", _) => {
                FluxAttrKind::TrustedImpl(
                    parse_yes_no_with_reason(attr_item)
                        .map_err(|_| invalid_attr_err(self))?
                        .into(),
                )
            }
            ("opaque", AttrArgs::Empty) => FluxAttrKind::Opaque,
            ("reflect", AttrArgs::Empty) => FluxAttrKind::Reflect,
            ("extern_spec", AttrArgs::Empty) => FluxAttrKind::ExternSpec,
            ("should_fail", AttrArgs::Empty) => FluxAttrKind::ShouldFail,
            _ => return Err(invalid_attr_err(self)),
        };
        Ok(FluxAttr { kind, span: attr_item.span() })
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
        if let Some(check_overflow) = attrs.infer_opts() {
            self.specs.infer_opts.insert(def_id, check_overflow);
        }
    }
}

fn parse_yes_no_with_reason(attr_item: &AttrItem) -> std::result::Result<bool, ()> {
    match attr_item.meta_kind().ok_or(())? {
        MetaItemKind::Word => Ok(true),
        MetaItemKind::List(items) => {
            let (b, items) = parse_opt_yes_no(&items, true);
            let (_, items) = parse_opt_reason(items);
            if items.is_empty() {
                Ok(b)
            } else {
                Err(())
            }
        }
        _ => Err(()),
    }
}

fn parse_opt_yes_no(items: &[MetaItemInner], default: bool) -> (bool, &[MetaItemInner]) {
    let [hd, tl @ ..] = items else { return (default, items) };
    if hd.is_word() {
        if hd.has_name(sym::yes) {
            (true, tl)
        } else if hd.has_name(sym::no) {
            (false, tl)
        } else {
            (default, items)
        }
    } else {
        (default, items)
    }
}

fn parse_opt_reason(items: &[MetaItemInner]) -> (Option<Symbol>, &[MetaItemInner]) {
    let [hd, tl @ ..] = items else { return (None, items) };
    if let Some(value) = hd.value_str()
        && hd.has_name(sym::reason)
    {
        (Some(value), tl)
    } else {
        (None, items)
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
    Trusted(Trusted),
    TrustedImpl(Trusted),
    Opaque,
    Reflect,
    FnSig(surface::FnSig),
    TraitAssocReft(surface::TraitAssocReft),
    ImplAssocReft(surface::ImplAssocReft),
    RefinedBy(surface::RefineParams),
    Generics(surface::Generics),
    QualNames(surface::QualNames),
    Items(Vec<surface::Item>),
    TypeAlias(surface::TyAlias),
    Field(surface::Ty),
    Constant(surface::ConstantInfo),
    Variant(surface::VariantDef),
    InferOpts(config::PartialInferOpts),
    Invariant(surface::Expr),
    Ignore(Ignored),
    ShouldFail,
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

    fn ty_alias(&mut self) -> Option<surface::TyAlias> {
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
    }

    fn impl_assoc_refts(&mut self) -> Vec<surface::ImplAssocReft> {
        read_attrs!(self, ImplAssocReft)
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
            FluxAttrKind::Field(_) => attr_name!(Field),
            FluxAttrKind::Constant(_) => attr_name!(Constant),
            FluxAttrKind::Variant(_) => attr_name!(Variant),
            FluxAttrKind::TypeAlias(_) => attr_name!(TypeAlias),
            FluxAttrKind::InferOpts(_) => attr_name!(InferOpts),
            FluxAttrKind::Ignore(_) => attr_name!(Ignore),
            FluxAttrKind::Invariant(_) => attr_name!(Invariant),
            FluxAttrKind::ShouldFail => attr_name!(ShouldFail),
            FluxAttrKind::ExternSpec => attr_name!(ExternSpec),
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
    // TODO: Ugly that we have to access the collector for error reporting
    fn parse(attr_item: &AttrItem) -> AttrMapErr<Self> {
        let mut map = Self { map: HashMap::new() };
        let meta_item_kind = attr_item.meta_kind();
        match meta_item_kind {
            Some(MetaItemKind::List(items)) => {
                for item in items {
                    map.parse_entry(&item)?;
                }
            }
            _ => {
                return Err(errors::AttrMapErr {
                    span: attr_item.span(),
                    message: "bad syntax".to_string(),
                })
            }
        };
        Ok(map)
    }

    fn parse_entry(&mut self, nested_item: &MetaItemInner) -> AttrMapErr {
        match nested_item {
            MetaItemInner::MetaItem(item) => {
                let name = item.name_or_empty().to_ident_string();
                let span = item.span;
                if !name.is_empty() {
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

mod errors {
    use flux_errors::E0999;
    use flux_macros::Diagnostic;
    use rustc_hir::def_id::DefId;
    use rustc_middle::ty::TyCtxt;
    use rustc_span::{symbol::Ident, Span};

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

    #[derive(Diagnostic)]
    #[diag(driver_syntax_err, code = E0999)]
    pub(super) struct SyntaxErr {
        #[primary_span]
        pub span: Span,
        pub msg: &'static str,
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
