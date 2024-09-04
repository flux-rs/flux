use std::collections::HashMap;

use flux_common::{
    iter::IterExt,
    result::{ErrorCollector, ResultExt},
};
use flux_config::{self as config, CrateConfig};
use flux_errors::{Errors, FluxSession};
use flux_middle::{
    fhir::{Ignored, Trusted},
    rustc::lowering::resolve_trait_ref_impl_id,
    Specs,
};
use flux_syntax::{surface, ParseResult, ParseSess};
use itertools::Itertools;
use rustc_ast::{
    tokenstream::TokenStream, AttrArgs, AttrItem, AttrKind, MetaItemKind, NestedMetaItem,
};
use rustc_ast_pretty::pprust::tts_to_string;
use rustc_errors::ErrorGuaranteed;
use rustc_hir::{
    self as hir,
    def::DefKind,
    def_id::{DefId, LocalDefId, CRATE_DEF_ID},
    AssocItemKind, EnumDef, GenericBounds, ImplItemKind, ImplItemRef, Item, ItemKind, OwnerId,
    VariantData,
};
use rustc_middle::ty::{TraitPredicate, TyCtxt};
use rustc_span::{Span, Symbol, SyntaxContext};

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
        hir::intravisit::walk_item(self, item);
    }

    fn visit_trait_item(&mut self, trait_item: &'tcx rustc_hir::TraitItem<'tcx>) {
        let _ = self.collect_trait_item(trait_item);
        hir::intravisit::walk_trait_item(self, trait_item);
    }

    fn visit_impl_item(&mut self, impl_item: &'tcx rustc_hir::ImplItem<'tcx>) {
        let _ = self.collect_impl_item(impl_item);
        hir::intravisit::walk_impl_item(self, impl_item);
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
        let mut attrs = self.parse_flux_attrs(CRATE_DEF_ID)?;
        self.report_dups(&attrs)?;
        self.collect_ignore_and_trusted(&mut attrs, CRATE_DEF_ID);
        self.specs.extend_items(attrs.items());
        self.specs.crate_config = attrs.crate_config();
        Ok(())
    }

    fn collect_item(&mut self, item: &'tcx Item<'tcx>) -> Result {
        let owner_id = item.owner_id;

        let mut attrs = self.parse_flux_attrs(owner_id.def_id)?;
        self.report_dups(&attrs)?;
        self.collect_ignore_and_trusted(&mut attrs, owner_id.def_id);

        match &item.kind {
            ItemKind::Fn(..) => self.collect_fn_spec(owner_id, attrs),
            ItemKind::Struct(variant, ..) => self.collect_structc_def(owner_id, attrs, variant),
            ItemKind::Enum(enum_def, ..) => self.collect_enum_def(owner_id, attrs, enum_def),
            ItemKind::Mod(..) => self.collect_mod(attrs),
            ItemKind::TyAlias(..) => self.collect_type_alias(owner_id, attrs),
            ItemKind::Impl(impl_) => self.collect_impl(owner_id, attrs, impl_),
            ItemKind::Trait(_, _, _, bounds, _) => self.collect_trait(owner_id, attrs, bounds),
            _ => Ok(()),
        }
    }

    fn collect_trait_item(&mut self, trait_item: &'tcx rustc_hir::TraitItem<'tcx>) -> Result {
        let owner_id = trait_item.owner_id;

        let mut attrs = self.parse_flux_attrs(owner_id.def_id)?;
        self.report_dups(&attrs)?;
        self.collect_ignore_and_trusted(&mut attrs, owner_id.def_id);

        if let rustc_hir::TraitItemKind::Fn(_, _) = trait_item.kind {
            self.collect_fn_spec(owner_id, attrs)?;
        }
        Ok(())
    }

    fn collect_impl_item(&mut self, impl_item: &'tcx rustc_hir::ImplItem<'tcx>) -> Result {
        let owner_id = impl_item.owner_id;

        let mut attrs = self.parse_flux_attrs(owner_id.def_id)?;
        self.report_dups(&attrs)?;
        self.collect_ignore_and_trusted(&mut attrs, owner_id.def_id);

        if let ImplItemKind::Fn(..) = &impl_item.kind {
            self.collect_fn_spec(owner_id, attrs)?;
        }
        Ok(())
    }

    fn collect_mod(&mut self, mut attrs: FluxAttrs) -> Result {
        self.specs.extend_items(attrs.items());
        Ok(())
    }

    fn collect_trait(
        &mut self,
        owner_id: OwnerId,
        mut attrs: FluxAttrs,
        bounds: &GenericBounds,
    ) -> Result {
        let generics = attrs.generics();
        let assoc_refinements = attrs.trait_assoc_refts();

        self.specs
            .traits
            .insert(owner_id, surface::Trait { generics, assoc_refinements });

        if attrs.extern_spec() {
            let extern_id =
                self.extract_extern_def_id_from_extern_spec_trait(owner_id.def_id, bounds)?;
            self.specs.insert_extern_id(owner_id.def_id, extern_id);
        };

        Ok(())
    }

    fn collect_impl(
        &mut self,
        owner_id: OwnerId,
        mut attrs: FluxAttrs,
        impl_: &rustc_hir::Impl,
    ) -> Result {
        let generics = attrs.generics();
        let assoc_refinements = attrs.impl_assoc_refts();

        if attrs.extern_spec()
            && let Some(extern_id) =
                self.extract_extern_def_id_from_extern_spec_impl(owner_id.def_id, impl_.items)
        {
            self.specs.insert_extern_id(owner_id.def_id, extern_id);
        }

        self.specs
            .impls
            .insert(owner_id, surface::Impl { generics, assoc_refinements });

        Ok(())
    }

    fn collect_type_alias(&mut self, owner_id: OwnerId, mut attrs: FluxAttrs) -> Result {
        self.specs.ty_aliases.insert(owner_id, attrs.ty_alias());
        Ok(())
    }

    fn collect_structc_def(
        &mut self,
        owner_id: OwnerId,
        mut attrs: FluxAttrs,
        data: &VariantData,
    ) -> Result {
        let mut opaque = attrs.opaque();
        let refined_by = attrs.refined_by();
        let generics = attrs.generics();

        let is_extern_spec = attrs.extern_spec();
        if is_extern_spec {
            // If there's only one field it corresponds to the special field to extract the struct
            // def_id. This means the user didn't specify any fields and thus we consider the struct
            // as opaque.
            opaque = data.fields().len() == 1;
            let extern_id =
                self.extract_extern_def_id_from_extern_spec_struct(owner_id.def_id, data)?;
            self.specs.insert_extern_id(owner_id.def_id, extern_id);
        }

        // For extern specs, we skip the last field containing the information to extract the def_id
        let fields = data
            .fields()
            .iter()
            .take(data.fields().len() - (is_extern_spec as usize))
            .map(|field| self.parse_field_spec(field, opaque))
            .try_collect_exhaust()?;

        let invariants = attrs.invariants();

        self.specs.structs.insert(
            owner_id,
            surface::StructDef {
                generics,
                refined_by,
                fields,
                opaque,
                invariants,
                node_id: self.parse_sess.next_node_id(),
            },
        );

        Ok(())
    }

    fn parse_field_spec(
        &mut self,
        field: &rustc_hir::FieldDef,
        opaque: bool,
    ) -> Result<Option<surface::Ty>> {
        let mut attrs = self.parse_flux_attrs(field.def_id)?;
        self.report_dups(&attrs)?;
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
    ) -> Result {
        let generics = attrs.generics();
        let refined_by = attrs.refined_by();

        let is_extern_spec = attrs.extern_spec();
        if is_extern_spec {
            let extern_id =
                self.extract_extern_def_id_from_extern_spec_enum(owner_id.def_id, enum_def)?;
            self.specs.insert_extern_id(owner_id.def_id, extern_id);
        }

        // For extern specs, we skip the last variant containing the information to extract the def_id
        let variants = enum_def
            .variants
            .iter()
            .take(enum_def.variants.len() - (is_extern_spec as usize))
            .map(|variant| self.collect_variant(variant, refined_by.is_some()))
            .try_collect_exhaust()?;

        let invariants = attrs.invariants();

        self.specs.enums.insert(
            owner_id,
            surface::EnumDef {
                generics,
                refined_by,
                variants,
                invariants,
                node_id: self.parse_sess.next_node_id(),
            },
        );
        Ok(())
    }

    fn collect_variant(
        &mut self,
        hir_variant: &rustc_hir::Variant,
        has_refined_by: bool,
    ) -> Result<Option<surface::VariantDef>> {
        let mut attrs = self.parse_flux_attrs(hir_variant.def_id)?;
        self.report_dups(&attrs)?;

        let variant = attrs.variant();

        if variant.is_none() && has_refined_by {
            return Err(self
                .errors
                .emit(errors::MissingVariant::new(hir_variant.span)));
        }

        Ok(variant)
    }

    fn collect_fn_spec(&mut self, owner_id: OwnerId, mut attrs: FluxAttrs) -> Result {
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

        let qual_names: Option<surface::QualNames> = attrs.qual_names();
        if attrs.extern_spec() {
            if fn_sig.is_none() {
                return Err(self.errors.emit(errors::MissingFnSigForExternSpec {
                    span: self.tcx.def_span(owner_id),
                }));
            }
            let extern_def_id = self.extract_extern_def_id_from_extern_spec_fn(owner_id.def_id)?;
            self.specs.insert_extern_id(owner_id.def_id, extern_def_id);
            // We should never check an extern spec (it will infinitely recurse)
        }
        self.specs
            .fn_sigs
            .insert(owner_id, surface::FnSpec { fn_sig, qual_names });
        Ok(())
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
        let invalid_attr_err = |this: &Self| -> Result<FluxAttr> {
            Err(this
                .errors
                .emit(errors::InvalidAttr { span: attr_item.span() }))
        };

        let [_, segment] = &attr_item.path.segments[..] else { return invalid_attr_err(self) };

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
                    _ => return invalid_attr_err(self),
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
            ("cfg", AttrArgs::Delimited(..)) => {
                let crate_cfg = FluxAttrCFG::parse_cfg(attr_item)
                    .emit(&self.errors)?
                    .try_into_crate_cfg()
                    .emit(&self.errors)?;
                FluxAttrKind::CrateConfig(crate_cfg)
            }
            ("ignore", AttrArgs::Empty) => FluxAttrKind::Ignore(Ignored::Yes),
            ("ignore", AttrArgs::Delimited(dargs)) => {
                let val = tts_to_string(&dargs.tokens);
                match &val[..] {
                    "yes" => FluxAttrKind::Ignore(Ignored::Yes),
                    "no" => FluxAttrKind::Ignore(Ignored::No),
                    _ => return invalid_attr_err(self),
                }
            }
            ("trusted", AttrArgs::Empty) => FluxAttrKind::Trusted(Trusted::Yes),
            ("trusted", AttrArgs::Delimited(dargs)) => {
                let val = tts_to_string(&dargs.tokens);
                match &val[..] {
                    "yes" => FluxAttrKind::Trusted(Trusted::Yes),
                    "no" => FluxAttrKind::Trusted(Trusted::No),
                    _ => return invalid_attr_err(self),
                }
            }
            ("opaque", AttrArgs::Empty) => FluxAttrKind::Opaque,
            ("fake_impl", AttrArgs::Empty) => FluxAttrKind::FakeImpl,
            ("extern_spec", AttrArgs::Empty) => FluxAttrKind::ExternSpec,
            _ => return invalid_attr_err(self),
        };
        Ok(FluxAttr { kind, span: attr_item.span() })
    }

    // In Prusti they suggested looking into doing this instead of using a Visitor...
    // it seems more brittle but I guess conversely their version is a little permissive.
    fn extract_extern_def_id_from_extern_spec_fn(&mut self, def_id: LocalDefId) -> Result<DefId> {
        use rustc_hir::{def, ExprKind, Node};
        // Regular functions
        if let Node::Item(i) = self.tcx.hir_node_by_def_id(def_id)
            && let ItemKind::Fn(_, _, body_id) = &i.kind
            && let Node::Expr(e) = self.tcx.hir_node(body_id.hir_id)
            && let ExprKind::Block(b, _) = e.kind
            && let Some(e) = b.expr
            && let ExprKind::Call(callee, _) = &e.kind
            && let ExprKind::Path(qself) = &callee.kind
        {
            let typeck_result = self.tcx.typeck(def_id);
            if let def::Res::Def(_, def_id) = typeck_result.qpath_res(qself, callee.hir_id) {
                return Ok(def_id);
            }
        }
        // impl functions
        if let Node::ImplItem(i) = self.tcx.hir_node_by_def_id(def_id)
            && let ImplItemKind::Fn(_, body_id) = &i.kind
            && let Node::Expr(e) = self.tcx.hir_node(body_id.hir_id)
            && let ExprKind::Block(b, _) = e.kind
            && let Some(e) = b.expr
            && let ExprKind::Call(callee, _) = &e.kind
            && let ExprKind::Path(qself) = &callee.kind
        {
            let typeck_result = self.tcx.typeck(def_id);

            if let rustc_middle::ty::FnDef(fn_def, args) =
                typeck_result.node_type(callee.hir_id).kind()
                && let Some((callee_id, _)) =
                    flux_middle::rustc::lowering::resolve_call_from(self.tcx, def_id, *fn_def, args)
            {
                return Ok(callee_id);
            }
            if let def::Res::Def(_, def_id) = typeck_result.qpath_res(qself, callee.hir_id) {
                return Ok(def_id);
            }
        }
        Err(self
            .errors
            .emit(errors::MalformedExternSpec { span: self.tcx.def_span(def_id) }))
    }

    fn extract_extern_def_id_from_extern_spec_struct(
        &mut self,
        def_id: LocalDefId,
        data: &VariantData,
    ) -> Result<DefId> {
        if let Some(extern_field) = data.fields().last() {
            let ty = self.tcx.type_of(extern_field.def_id);
            if let Some(adt_def) = ty.skip_binder().ty_adt_def() {
                return Ok(adt_def.did());
            }
        }
        Err(self
            .errors
            .emit(errors::MalformedExternSpec { span: self.tcx.def_span(def_id) }))
    }

    fn extract_extern_def_id_from_extern_spec_enum(
        &mut self,
        def_id: LocalDefId,
        enum_def: &EnumDef,
    ) -> Result<DefId> {
        if let Some(fake) = enum_def.variants.last() {
            return self.extract_extern_def_id_from_extern_spec_struct(def_id, &fake.data);
        }
        Err(self
            .errors
            .emit(errors::MalformedExternSpec { span: self.tcx.def_span(def_id) }))
    }

    fn fake_method_of(&mut self, items: &[ImplItemRef]) -> Option<LocalDefId> {
        for item in items {
            if let Ok(mut attrs) = self.parse_flux_attrs(item.id.owner_id.def_id) {
                if let AssocItemKind::Fn { .. } = item.kind
                    && attrs.fake_impl()
                {
                    return Some(item.id.owner_id.def_id);
                }
            }
        }
        None
    }

    fn is_good_trait_predicate(&self, trait_predicate: &TraitPredicate) -> bool {
        let def_id = trait_predicate.trait_ref.def_id;
        // !pretty::def_id_to_string(def_id).contains("Sized") // TODO: use LangItem::Sized?

        self.tcx.require_lang_item(rustc_hir::LangItem::Sized, None) != def_id
    }

    /// Given as input a fake_method_def_id `fake` where
    ///     `fn fake<A: Trait<..>>(x: Ty) {}`
    /// we want to
    /// 1. build the [`TraitRef`] for `<Ty as Trait<...>>` and then
    /// 2. query [resolve_trait_ref_impl_id] to get the impl_id for the above trait-implementation.
    ///
    /// [`TraitRef`]: rustc_middle::ty::TraitRef
    fn extract_extern_def_id_from_extern_spec_impl(
        &mut self,
        _def_id: LocalDefId,
        items: &[ImplItemRef],
    ) -> Option<DefId> {
        // 1. Find the fake_method's def_id
        let fake_method_def_id = self.fake_method_of(items)?;

        // 2. Get the fake_method's input type
        let ty = self
            .tcx
            .fn_sig(fake_method_def_id)
            .instantiate_identity()
            .skip_binder()
            .inputs()
            .first()
            .unwrap();
        let arg = rustc_middle::ty::GenericArg::from(*ty);

        // 3. Get the fake_method's trait_ref
        let trait_ref = {
            // let _generics = self.tcx.generics_of(fake_method_def_id);
            self.tcx
                .predicates_of(fake_method_def_id)
                .predicates
                .iter()
                .filter_map(|(c, _)| c.as_trait_clause()?.no_bound_vars())
                .find(|p| self.is_good_trait_predicate(p))
                .unwrap()
                .trait_ref
        };

        // 4. Splice in the type from step 2 to create query trait_ref
        let mut args = vec![arg];
        for arg in trait_ref.args.as_slice().iter().skip(1) {
            args.push(*arg);
        }
        let trait_ref = rustc_middle::ty::TraitRef::new(self.tcx, trait_ref.def_id, args);

        // 5. Resolve the trait_ref to an impl_id
        let (impl_id, _) =
            resolve_trait_ref_impl_id(self.tcx, fake_method_def_id, trait_ref).unwrap();
        Some(impl_id)
    }

    fn extract_extern_def_id_from_extern_spec_trait(
        &mut self,
        def_id: LocalDefId,
        bounds: &GenericBounds,
    ) -> Result<DefId> {
        if let Some(bound) = bounds.first()
            && let Some(trait_ref) = bound.trait_ref()
            && let Some(trait_id) = trait_ref.trait_def_id()
        {
            Ok(trait_id)
        } else {
            Err(self
                .errors
                .emit(errors::MalformedExternSpec { span: self.tcx.def_span(def_id) }))
        }
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
    Opaque,
    FnSig(surface::FnSig),
    TraitAssocReft(surface::TraitAssocReft),
    ImplAssocReft(surface::ImplAssocReft),
    RefinedBy(surface::RefineParams),
    Generics(surface::Generics),
    QualNames(surface::QualNames),
    Items(Vec<surface::Item>),
    TypeAlias(surface::TyAlias),
    Field(surface::Ty),
    Variant(surface::VariantDef),
    CrateConfig(config::CrateConfig),
    Invariant(surface::Expr),
    Ignore(Ignored),
    FakeImpl,
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

    fn ignore(&mut self) -> Option<Ignored> {
        read_attr!(self, Ignore)
    }

    fn fake_impl(&mut self) -> bool {
        read_flag!(self, FakeImpl)
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
}

impl FluxAttrKind {
    fn name(&self) -> &'static str {
        match self {
            FluxAttrKind::Trusted(_) => attr_name!(Trusted),
            FluxAttrKind::Opaque => attr_name!(Opaque),
            FluxAttrKind::FnSig(_) => attr_name!(FnSig),
            FluxAttrKind::TraitAssocReft(_) => attr_name!(TraitAssocReft),
            FluxAttrKind::ImplAssocReft(_) => attr_name!(ImplAssocReft),
            FluxAttrKind::RefinedBy(_) => attr_name!(RefinedBy),
            FluxAttrKind::Generics(_) => attr_name!(Generics),
            FluxAttrKind::Items(_) => attr_name!(Items),
            FluxAttrKind::QualNames(_) => attr_name!(QualNames),
            FluxAttrKind::Field(_) => attr_name!(Field),
            FluxAttrKind::Variant(_) => attr_name!(Variant),
            FluxAttrKind::TypeAlias(_) => attr_name!(TypeAlias),
            FluxAttrKind::CrateConfig(_) => attr_name!(CrateConfig),
            FluxAttrKind::Ignore(_) => attr_name!(Ignore),
            FluxAttrKind::Invariant(_) => attr_name!(Invariant),
            FluxAttrKind::ExternSpec => attr_name!(ExternSpec),
            FluxAttrKind::FakeImpl => attr_name!(FakeImpl),
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

type CFGResult<T = ()> = std::result::Result<T, errors::CFGError>;

impl FluxAttrCFG {
    // TODO: Ugly that we have to access the collector for error reporting
    fn parse_cfg(attr_item: &AttrItem) -> CFGResult<Self> {
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
        Ok(cfg)
    }

    fn parse_cfg_item(&mut self, nested_item: &NestedMetaItem) -> CFGResult {
        match nested_item {
            NestedMetaItem::MetaItem(item) => {
                let name = item.name_or_empty().to_ident_string();
                let span = item.span;
                if !name.is_empty() {
                    if self.map.contains_key(&name) {
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

    fn try_into_crate_cfg(&mut self) -> CFGResult<config::CrateConfig> {
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
    #[diag(driver_cfg_error, code = E0999)]
    pub(super) struct CFGError {
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
    #[diag(driver_malformed_extern_spec, code = E0999)]
    pub(super) struct MalformedExternSpec {
        #[primary_span]
        pub span: Span,
    }

    #[derive(Diagnostic)]
    #[diag(driver_missing_fn_sig_for_extern_spec, code = E0999)]
    pub(super) struct MissingFnSigForExternSpec {
        #[primary_span]
        pub span: Span,
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
