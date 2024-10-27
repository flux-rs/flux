use std::iter;

use flux_common::{bug, dbg, index::IndexGen, iter::IterExt, span_bug};
use flux_config as config;
use flux_errors::FluxSession;
use flux_middle::{
    fhir::{self, lift::LiftCtxt, ExprRes, FhirId, FluxOwnerId, Res},
    global_env::GlobalEnv,
    try_alloc_slice, MaybeExternId, ResolverOutput,
};
use flux_syntax::{
    surface::{self, visit::Visitor as _, NodeId},
    walk_list,
};
use hir::{def::DefKind, ItemKind};
use rustc_data_structures::{fx::FxIndexSet, unord::UnordMap};
use rustc_errors::{Diagnostic, ErrorGuaranteed};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_hir::{self as hir, OwnerId, ParamName};
use rustc_span::{
    def_id::{DefId, LocalDefId},
    sym,
    symbol::kw,
    Span, Symbol, DUMMY_SP,
};

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

use crate::{errors, resolver::refinement_resolver::SORTS};

pub(crate) fn desugar_qualifier<'genv>(
    genv: GlobalEnv<'genv, '_>,
    resolver_output: &'genv ResolverOutput,
    qualifier: &surface::Qualifier,
) -> Result<fhir::Qualifier<'genv>> {
    let mut cx = FluxItemCtxt::new(genv, resolver_output, qualifier.name.name);
    let expr = cx.desugar_expr(&qualifier.expr);

    Ok(fhir::Qualifier {
        name: qualifier.name.name,
        args: cx.desugar_refine_params(&qualifier.params),
        global: qualifier.global,
        expr: expr?,
    })
}

pub(crate) fn desugar_spec_func<'genv>(
    genv: GlobalEnv<'genv, '_>,
    resolver_output: &'genv ResolverOutput,
    spec_func: &surface::SpecFunc,
) -> Result<fhir::SpecFunc<'genv>> {
    let mut cx = FluxItemCtxt::new(genv, resolver_output, spec_func.name.name);
    let body = spec_func
        .body
        .as_ref()
        .map(|body| cx.desugar_expr(body))
        .transpose()?;
    let name = spec_func.name.name;
    let params = spec_func.sort_vars.len();
    let sort = cx.desugar_sort(&spec_func.output, None);
    let args = cx.desugar_refine_params(&spec_func.params);

    Ok(fhir::SpecFunc { name, params, args, sort, body })
}

/// Collect all sorts resolved to a generic type in a list of refinement parameters. Return the set
/// of generic def_ids used (sorted by their position in the list of generics).
fn collect_generics_in_params(
    genv: GlobalEnv,
    owner: MaybeExternId<OwnerId>,
    resolver_output: &ResolverOutput,
    params: &surface::RefineParams,
) -> FxIndexSet<DefId> {
    struct ParamCollector<'a> {
        resolver_output: &'a ResolverOutput,
        found: FxHashSet<DefId>,
    }
    impl surface::visit::Visitor for ParamCollector<'_> {
        fn visit_base_sort(&mut self, bsort: &surface::BaseSort) {
            if let surface::BaseSort::Path(path) = bsort {
                let res = self.resolver_output.sort_path_res_map[&path.node_id];
                if let fhir::SortRes::TyParam(def_id) = res {
                    self.found.insert(def_id);
                }
            }
            surface::visit::walk_base_sort(self, bsort);
        }
    }
    let mut vis = ParamCollector { resolver_output, found: FxHashSet::default() };
    walk_list!(vis, visit_refine_param, params);
    genv.tcx()
        .generics_of(owner.resolved_id())
        .own_params
        .iter()
        .filter_map(
            |param| if vis.found.contains(&param.def_id) { Some(param.def_id) } else { None },
        )
        .collect()
}

pub(crate) struct RustItemCtxt<'a, 'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    local_id_gen: IndexGen<fhir::ItemLocalId>,
    owner: MaybeExternId<OwnerId>,
    fn_sig_scope: Option<NodeId>,
    resolver_output: &'genv ResolverOutput,
    opaque_tys: Option<&'a mut UnordMap<LocalDefId, fhir::Item<'genv>>>,
}

struct FluxItemCtxt<'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    resolver_output: &'genv ResolverOutput,
    local_id_gen: IndexGen<fhir::ItemLocalId>,
    owner: Symbol,
}

impl<'a, 'genv, 'tcx: 'genv> RustItemCtxt<'a, 'genv, 'tcx> {
    pub(crate) fn new(
        genv: GlobalEnv<'genv, 'tcx>,
        owner: MaybeExternId<OwnerId>,
        resolver_output: &'genv ResolverOutput,
        opaque_tys: Option<&'a mut UnordMap<LocalDefId, fhir::Item<'genv>>>,
    ) -> Self {
        RustItemCtxt {
            genv,
            owner,
            fn_sig_scope: None,
            local_id_gen: IndexGen::new(),
            resolver_output,
            opaque_tys,
        }
    }

    fn with_new_owner<'b>(
        &'b mut self,
        owner: MaybeExternId<OwnerId>,
    ) -> RustItemCtxt<'b, 'genv, 'tcx> {
        RustItemCtxt::new(self.genv, owner, self.resolver_output, self.opaque_tys.as_deref_mut())
    }

    fn as_lift_cx<'b>(&'b mut self) -> LiftCtxt<'b, 'genv, 'tcx> {
        LiftCtxt::new(self.genv, self.owner, &self.local_id_gen, self.opaque_tys.as_deref_mut())
    }

    pub(crate) fn desugar_trait(&mut self, trait_: &surface::Trait) -> Result<fhir::Item<'genv>> {
        let generics = if let Some(generics) = &trait_.generics {
            self.desugar_generics(generics)?
        } else {
            self.as_lift_cx().lift_generics()?
        };
        let assoc_refinements = self.desugar_trait_assoc_refts(&trait_.assoc_refinements)?;
        let trait_ = fhir::Trait { assoc_refinements };

        if config::dump_fhir() {
            dbg::dump_item_info(self.genv.tcx(), self.owner.local_id(), "fhir", &trait_).unwrap();
        }

        Ok(fhir::Item { generics, kind: fhir::ItemKind::Trait(trait_), owner_id: self.owner })
    }

    fn desugar_trait_assoc_refts(
        &mut self,
        assoc_refts: &[surface::TraitAssocReft],
    ) -> Result<&'genv [fhir::TraitAssocReft<'genv>]> {
        try_alloc_slice!(self.genv, assoc_refts, |assoc_reft| {
            let name = assoc_reft.name.name;
            let params = self.desugar_refine_params(&assoc_reft.params);
            let output = self.desugar_base_sort(&assoc_reft.output, None);
            let body = match &assoc_reft.body {
                Some(expr) => Some(self.desugar_expr(expr)?),
                None => None,
            };
            Ok(fhir::TraitAssocReft { name, params, output, body, span: assoc_reft.span })
        })
    }

    pub(crate) fn desugar_impl(&mut self, impl_: &surface::Impl) -> Result<fhir::Item<'genv>> {
        let generics = if let Some(generics) = &impl_.generics {
            self.desugar_generics(generics)?
        } else {
            self.as_lift_cx().lift_generics()?
        };
        let assoc_refinements = self.desugar_impl_assoc_refts(&impl_.assoc_refinements)?;
        let impl_ = fhir::Impl { assoc_refinements };

        if config::dump_fhir() {
            dbg::dump_item_info(self.genv.tcx(), self.owner.local_id(), "fhir", &impl_).unwrap();
        }

        Ok(fhir::Item { generics, kind: fhir::ItemKind::Impl(impl_), owner_id: self.owner })
    }

    fn desugar_impl_assoc_refts(
        &mut self,
        assoc_refts: &[surface::ImplAssocReft],
    ) -> Result<&'genv [fhir::ImplAssocReft<'genv>]> {
        try_alloc_slice!(self.genv, assoc_refts, |assoc_reft| {
            let name = assoc_reft.name.name;
            let body = self.desugar_expr(&assoc_reft.body)?;
            let params = self.desugar_refine_params(&assoc_reft.params);
            let output = self.desugar_base_sort(&assoc_reft.output, None);
            Ok(fhir::ImplAssocReft { name, params, output, body, span: assoc_reft.span })
        })
    }

    pub(crate) fn desugar_generics(
        &mut self,
        generics: &surface::Generics,
    ) -> Result<fhir::Generics<'genv>> {
        let hir_generics = self
            .genv
            .hir()
            .get_generics(self.owner.local_id().def_id)
            .unwrap();

        // 1. Collect generic type parameters by their name
        let hir_params_map: FxHashMap<_, _> = hir_generics
            .params
            .iter()
            .flat_map(|param| {
                if let hir::ParamName::Plain(name) = param.name
                    && let hir::GenericParamKind::Type { default, .. } = param.kind
                {
                    Some((name, (param.def_id, default)))
                } else {
                    None
                }
            })
            .collect();

        // 2. Desugar surface params and resolve them to their corresponding def id or self param.
        let mut surface_params = FxHashMap::default();
        let mut self_kind = None;
        for param in &generics.params {
            if param.name.name == kw::SelfUpper {
                let kind = match &param.kind {
                    surface::GenericParamKind::Type => {
                        fhir::GenericParamKind::Type { default: None }
                    }
                    surface::GenericParamKind::Base => fhir::GenericParamKind::Base,
                };
                self_kind = Some(kind);
            } else {
                let Some(&(def_id, default)) = hir_params_map.get(&param.name) else {
                    return Err(self.emit_err(errors::UnresolvedGenericParam::new(param.name)));
                };

                let maybe_extern = self.genv.maybe_extern_id(def_id);
                let kind = match &param.kind {
                    surface::GenericParamKind::Type => {
                        fhir::GenericParamKind::Type {
                            default: if maybe_extern.is_local() {
                                default
                                    .map(|ty| self.as_lift_cx().lift_ty(ty))
                                    .transpose()?
                            } else {
                                None
                            },
                        }
                    }
                    surface::GenericParamKind::Base => fhir::GenericParamKind::Base,
                };
                surface_params.insert(
                    def_id,
                    fhir::GenericParam {
                        def_id: maybe_extern,
                        name: ParamName::Plain(param.name),
                        kind,
                    },
                );
            }
        }

        // 3. Return desugared generic if we have one or else lift it from hir
        let params = try_alloc_slice!(self.genv, hir_generics.params, |hir_param| {
            if let Some(surface_param) = surface_params.remove(&hir_param.def_id) {
                Ok(surface_param)
            } else {
                self.as_lift_cx().lift_generic_param(hir_param)
            }
        })?;

        let predicates = self.desugar_generic_predicates(&generics.predicates)?;
        Ok(fhir::Generics { params, self_kind, refinement_params: &[], predicates })
    }

    fn desugar_generic_predicates(
        &mut self,
        predicates: &[surface::WhereBoundPredicate],
    ) -> Result<&'genv [fhir::WhereBoundPredicate<'genv>]> {
        try_alloc_slice!(self.genv, predicates, |pred| {
            let bounded_ty = self.desugar_ty(&pred.bounded_ty)?;
            let bounds = self.desugar_generic_bounds(&pred.bounds)?;
            Ok(fhir::WhereBoundPredicate { span: pred.span, bounded_ty, bounds })
        })
    }

    fn desugar_generic_bounds(
        &mut self,
        bounds: &[surface::TraitRef],
    ) -> Result<fhir::GenericBounds<'genv>> {
        try_alloc_slice!(self.genv, bounds, |bound| {
            Ok(fhir::GenericBound::Trait(
                self.desugar_trait_ref(bound)?,
                fhir::TraitBoundModifier::None,
            ))
        })
    }

    fn desugar_trait_ref(
        &mut self,
        trait_ref: &surface::TraitRef,
    ) -> Result<fhir::PolyTraitRef<'genv>> {
        let fhir::QPath::Resolved(None, path) = self.desugar_qpath(None, &trait_ref.path)? else {
            span_bug!(trait_ref.path.span, "desugar_alias_reft: unexpected qpath")
        };
        let span = path.span;
        Ok(fhir::PolyTraitRef { bound_generic_params: &[], trait_ref: path, span })
    }

    fn desugar_refined_by(
        &mut self,
        refined_by: &surface::RefineParams,
    ) -> Result<fhir::RefinedBy<'genv>> {
        let generic_id_to_var_idx =
            collect_generics_in_params(self.genv, self.owner, self.resolver_output, refined_by);

        let fields = refined_by
            .iter()
            .map(|param| {
                (param.ident.name, self.desugar_sort(&param.sort, Some(&generic_id_to_var_idx)))
            })
            .collect();

        Ok(fhir::RefinedBy::new(fields, generic_id_to_var_idx))
    }

    pub(crate) fn desugar_struct_def(
        &mut self,
        struct_def: &surface::StructDef,
    ) -> Result<fhir::Item<'genv>> {
        let refined_by = if let Some(refined_by) = &struct_def.refined_by {
            self.desugar_refined_by(refined_by)?
        } else {
            self.as_lift_cx().lift_refined_by()
        };

        let generics = self.desugar_generics_for_adt(struct_def.generics.as_ref(), &refined_by)?;

        let invariants = try_alloc_slice!(self.genv, &struct_def.invariants, |invariant| {
            self.desugar_expr(invariant)
        })?;

        let kind = if struct_def.opaque {
            fhir::StructKind::Opaque
        } else {
            let kind = &self
                .genv
                .hir()
                .expect_item(self.owner.local_id().def_id)
                .kind;
            match kind {
                hir::ItemKind::Struct(variant_data, _) | hir::ItemKind::Union(variant_data, _) => {
                    debug_assert_eq!(struct_def.fields.len(), variant_data.fields().len());
                    let fields = try_alloc_slice!(
                        self.genv,
                        iter::zip(&struct_def.fields, variant_data.fields()),
                        |(ty, hir_field)| {
                            if let Some(ty) = ty {
                                Ok(fhir::FieldDef { ty: self.desugar_ty(ty)?, lifted: false })
                            } else {
                                self.as_lift_cx().lift_field_def(hir_field)
                            }
                        },
                    )?;
                    fhir::StructKind::Transparent { fields }
                }
                _ => bug!("expected struct or union"),
            }
        };

        let params = self.desugar_refine_params(struct_def.refined_by.as_deref().unwrap_or(&[]));
        let struct_def =
            fhir::StructDef { refined_by: self.genv.alloc(refined_by), params, kind, invariants };

        if config::dump_fhir() {
            dbg::dump_item_info(self.genv.tcx(), self.owner.local_id(), "fhir", struct_def)
                .unwrap();
        }

        Ok(fhir::Item { generics, kind: fhir::ItemKind::Struct(struct_def), owner_id: self.owner })
    }

    pub(crate) fn desugar_enum_def(
        &mut self,
        enum_def: &surface::EnumDef,
    ) -> Result<fhir::Item<'genv>> {
        let def_id = self.owner.local_id().def_id;
        let ItemKind::Enum(hir_enum, _) = self.genv.hir().expect_item(def_id).kind else {
            bug!("expected enum");
        };
        let variants = try_alloc_slice!(
            self.genv,
            iter::zip(&enum_def.variants, hir_enum.variants),
            |(variant, hir_variant)| self.desugar_enum_variant_def(variant, hir_variant)
        )?;

        let refined_by = if let Some(refined_by) = &enum_def.refined_by {
            self.desugar_refined_by(refined_by)?
        } else {
            self.as_lift_cx().lift_refined_by()
        };

        let generics = self.desugar_generics_for_adt(enum_def.generics.as_ref(), &refined_by)?;

        let invariants = try_alloc_slice!(self.genv, &enum_def.invariants, |invariant| {
            self.desugar_expr(invariant)
        })?;

        let params = self.desugar_refine_params(enum_def.refined_by.as_deref().unwrap_or(&[]));
        let enum_def =
            fhir::EnumDef { refined_by: self.genv.alloc(refined_by), params, variants, invariants };

        if config::dump_fhir() {
            dbg::dump_item_info(self.genv.tcx(), self.owner.local_id(), "fhir", &enum_def).unwrap();
        }

        Ok(fhir::Item { generics, kind: fhir::ItemKind::Enum(enum_def), owner_id: self.owner })
    }

    fn desugar_enum_variant_def(
        &mut self,
        variant_def: &Option<surface::VariantDef>,
        hir_variant: &hir::Variant,
    ) -> Result<fhir::VariantDef<'genv>> {
        if let Some(variant_def) = variant_def {
            let fields = try_alloc_slice!(self.genv, &variant_def.fields, |ty| {
                Ok(fhir::FieldDef { ty: self.desugar_ty(ty)?, lifted: false })
            })?;

            let ret = if let Some(ret) = &variant_def.ret {
                self.desugar_variant_ret(ret)?
            } else {
                self.as_lift_cx().lift_variant_ret()
            };

            let params = self
                .genv
                .alloc_slice_fill_iter(self.implicit_params_to_params(variant_def.node_id));
            Ok(fhir::VariantDef {
                def_id: hir_variant.def_id,
                params,
                fields,
                ret,
                span: variant_def.span,
                lifted: false,
            })
        } else {
            self.as_lift_cx().lift_enum_variant(hir_variant)
        }
    }

    fn desugar_generics_for_adt(
        &mut self,
        generics: Option<&surface::Generics>,
        refined_by: &fhir::RefinedBy,
    ) -> Result<fhir::Generics<'genv>> {
        Ok(if let Some(generics) = generics {
            self.desugar_generics(generics)?
        } else {
            self.as_lift_cx().lift_generics()?
        }
        .with_refined_by(self.genv, refined_by))
    }

    pub(crate) fn desugar_type_alias(
        &mut self,
        ty_alias: Option<&surface::TyAlias>,
    ) -> Result<fhir::Item<'genv>> {
        let Some(ty_alias) = ty_alias else {
            return self.as_lift_cx().lift_type_alias();
        };

        let refined_by = self.desugar_refined_by(&ty_alias.refined_by)?;
        let mut generics = self.desugar_generics(&ty_alias.generics)?;

        let ty = self.desugar_ty(&ty_alias.ty)?;

        generics.refinement_params = self.desugar_refine_params(&ty_alias.params);

        let params = self.desugar_refine_params(&ty_alias.refined_by);

        let ty_alias = fhir::TyAlias {
            refined_by: self.genv.alloc(refined_by),
            params,
            ty,
            span: ty_alias.span,
            lifted: false,
        };

        if config::dump_fhir() {
            dbg::dump_item_info(self.genv.tcx(), self.owner.local_id(), "fhir", &ty_alias).unwrap();
        }

        Ok(fhir::Item { generics, kind: fhir::ItemKind::TyAlias(ty_alias), owner_id: self.owner })
    }

    pub(crate) fn desugar_trait_assoc_ty(&mut self) -> Result<fhir::TraitItem<'genv>> {
        let generics = self.as_lift_cx().lift_generics()?;
        Ok(fhir::TraitItem { generics, kind: fhir::TraitItemKind::Type, owner_id: self.owner })
    }

    pub(crate) fn desugar_impl_assoc_ty(&mut self) -> Result<fhir::ImplItem<'genv>> {
        let generics = self.as_lift_cx().lift_generics()?;
        Ok(fhir::ImplItem { generics, kind: fhir::ImplItemKind::Type, owner_id: self.owner })
    }

    pub(crate) fn desugar_item_fn(
        &mut self,
        fn_spec: &surface::FnSpec,
    ) -> Result<fhir::Item<'genv>> {
        let (generics, fn_sig) = self.desugar_fn_spec(fn_spec)?;
        Ok(fhir::Item { generics, kind: fhir::ItemKind::Fn(fn_sig), owner_id: self.owner })
    }

    pub(crate) fn desugar_trait_fn(
        &mut self,
        fn_spec: &surface::FnSpec,
    ) -> Result<fhir::TraitItem<'genv>> {
        let (generics, fn_sig) = self.desugar_fn_spec(fn_spec)?;
        Ok(fhir::TraitItem {
            generics,
            kind: fhir::TraitItemKind::Fn(fn_sig),
            owner_id: self.owner,
        })
    }

    pub(crate) fn desugar_impl_fn(
        &mut self,
        fn_spec: &surface::FnSpec,
    ) -> Result<fhir::ImplItem<'genv>> {
        let (generics, fn_sig) = self.desugar_fn_spec(fn_spec)?;
        Ok(fhir::ImplItem { generics, kind: fhir::ImplItemKind::Fn(fn_sig), owner_id: self.owner })
    }

    pub(crate) fn desugar_fn_spec(
        &mut self,
        fn_spec: &surface::FnSpec,
    ) -> Result<(fhir::Generics<'genv>, fhir::FnSig<'genv>)> {
        let mut header = self.as_lift_cx().lift_fn_header();
        let (generics, decl) = if let Some(fn_sig) = &fn_spec.fn_sig {
            self.fn_sig_scope = Some(fn_sig.node_id);

            let mut requires = vec![];

            let mut generics = self.desugar_generics(&fn_sig.generics)?;

            for surface_requires in &fn_sig.requires {
                let params = self.desugar_refine_params(&surface_requires.params);
                let pred = self.desugar_expr(&surface_requires.pred)?;
                requires.push(fhir::Requires { params, pred });
            }

            // Bail out if there's an error in the arguments to avoid confusing error messages
            let inputs =
                try_alloc_slice!(self.genv, &fn_sig.inputs, |arg| self.desugar_fn_input(arg))?;

            let output = self.desugar_fn_output(fn_sig.asyncness, &fn_sig.output)?;

            generics.refinement_params = self.desugar_fn_sig_refine_params(fn_sig);

            let decl = fhir::FnDecl {
                requires: self.genv.alloc_slice(&requires),
                inputs,
                output,
                span: fn_sig.span,
                lifted: false,
            };
            // Fix up the span in asyncness
            if let surface::Async::Yes { span, .. } = fn_sig.asyncness {
                header.asyncness = hir::IsAsync::Async(span);
            }
            (generics, decl)
        } else {
            (self.as_lift_cx().lift_generics()?, self.as_lift_cx().lift_fn_decl()?)
        };
        if config::dump_fhir() {
            dbg::dump_item_info(self.genv.tcx(), self.owner.local_id(), "fhir", decl).unwrap();
        }

        let qual_names = fn_spec.qual_names.as_ref().map_or(&[][..], |it| &it.names);
        Ok((
            generics,
            fhir::FnSig {
                header,
                qualifiers: self.genv.alloc_slice(qual_names),
                decl: self.genv.alloc(decl),
            },
        ))
    }

    fn desugar_fn_sig_refine_params(
        &self,
        fn_sig: &surface::FnSig,
    ) -> &'genv [fhir::RefineParam<'genv>] {
        let explicit = self.desugar_refine_params_iter(&fn_sig.params);
        let implicit = self.implicit_params_to_params(fn_sig.node_id);

        self.genv.alloc_slice_with_capacity(
            explicit.len() + implicit.len(),
            explicit.into_iter().chain(implicit),
        )
    }

    fn desugar_fn_output(
        &mut self,
        asyncness: surface::Async,
        output: &surface::FnOutput,
    ) -> Result<fhir::FnOutput<'genv>> {
        let ret = self.desugar_asyncness(asyncness, &output.returns);

        let ensures = try_alloc_slice!(self.genv, &output.ensures, |it| self.desugar_ensures(it))?;

        let params = self
            .genv
            .alloc_slice_fill_iter(self.implicit_params_to_params(output.node_id));
        Ok(fhir::FnOutput { params, ret: ret?, ensures })
    }

    fn desugar_ensures(&mut self, cstr: &surface::Ensures) -> Result<fhir::Ensures<'genv>> {
        match cstr {
            surface::Ensures::Type(loc, ty, node_id) => {
                let res = self.desugar_loc(*loc, *node_id)?;
                let path = fhir::PathExpr {
                    segments: self.genv().alloc_slice(&[*loc]),
                    res,
                    fhir_id: self.next_fhir_id(),
                    span: loc.span,
                };
                let ty = self.desugar_ty(ty)?;
                Ok(fhir::Ensures::Type(path, ty))
            }
            surface::Ensures::Pred(e) => {
                let pred = self.desugar_expr(e)?;
                Ok(fhir::Ensures::Pred(pred))
            }
        }
    }

    fn desugar_fn_input(&mut self, input: &surface::FnInput) -> Result<fhir::Ty<'genv>> {
        match input {
            surface::FnInput::Constr(bind, path, pred, node_id) => {
                let bty = self.desugar_path_to_bty(None, path)?;

                let pred = self.desugar_expr(pred)?;

                let ty = if let Some(idx) = self.implicit_param_into_refine_arg(*bind, *node_id) {
                    fhir::Ty { kind: fhir::TyKind::Indexed(bty, idx), span: path.span }
                } else {
                    fhir::Ty { kind: fhir::TyKind::BaseTy(bty), span: path.span }
                };

                let span = path.span.to(pred.span);
                let kind = fhir::TyKind::Constr(pred, self.genv.alloc(ty));
                Ok(fhir::Ty { kind, span })
            }
            surface::FnInput::StrgRef(loc, ty, node_id) => {
                let span = loc.span;
                let (id, kind) = self.resolve_implicit_param(*node_id).unwrap();
                let path = fhir::PathExpr {
                    segments: self.genv.alloc_slice(&[*loc]),
                    res: ExprRes::Param(kind, id),
                    fhir_id: self.next_fhir_id(),
                    span: loc.span,
                };
                let ty = self.desugar_ty(ty)?;
                let kind = fhir::TyKind::StrgRef(
                    self.mk_lft_hole(),
                    self.genv.alloc(path),
                    self.genv.alloc(ty),
                );
                Ok(fhir::Ty { kind, span })
            }
            surface::FnInput::Ty(bind, ty, node_id) => {
                if let Some(bind) = bind
                    && let surface::TyKind::Base(bty) = &ty.kind
                {
                    let bty = self.desugar_bty(bty)?;
                    let kind =
                        if let Some(idx) = self.implicit_param_into_refine_arg(*bind, *node_id) {
                            fhir::TyKind::Indexed(bty, idx)
                        } else {
                            fhir::TyKind::BaseTy(bty)
                        };
                    Ok(fhir::Ty { kind, span: ty.span })
                } else {
                    self.desugar_ty(ty)
                }
            }
        }
    }

    fn desugar_asyncness(
        &mut self,
        asyncness: surface::Async,
        returns: &surface::FnRetTy,
    ) -> Result<fhir::Ty<'genv>> {
        match asyncness {
            surface::Async::Yes { node_id, span } => {
                let item_id = self.resolver_output.impl_trait_res_map[&node_id];
                let def_id = item_id.owner_id.def_id;
                let res = Res::Def(DefKind::OpaqueTy, def_id.to_def_id());

                // FIXME(nilehmann) since we can only pass local ids for opaque types it means we
                // can't support extern specs with opaque types.
                let opaque_ty = self
                    .with_new_owner(MaybeExternId::Local(item_id.owner_id))
                    .desugar_opaque_ty_for_async(returns)?;
                self.insert_opaque_ty(item_id.owner_id.def_id, opaque_ty);

                let (args, _) = self.desugar_generic_args(res, &[])?;
                let item_id = hir::ItemId { owner_id: hir::OwnerId { def_id } };
                let refine_args = self.implicit_params_to_args(self.fn_sig_scope.unwrap());
                let kind = fhir::TyKind::OpaqueDef(item_id, args, refine_args, false);
                Ok(fhir::Ty { kind, span })
            }
            surface::Async::No => Ok(self.desugar_fn_ret_ty(returns)?),
        }
    }

    fn desugar_opaque_ty_for_async(
        &mut self,
        returns: &surface::FnRetTy,
    ) -> Result<fhir::Item<'genv>> {
        let output = self.desugar_fn_ret_ty(returns)?;
        // Does this opaque type have any generics?
        let generics = self.as_lift_cx().lift_generics()?;
        let trait_ref = self.make_lang_item_path(
            hir::LangItem::Future,
            DUMMY_SP,
            &[],
            self.genv.alloc_slice(&[fhir::AssocItemConstraint {
                ident: surface::Ident::with_dummy_span(sym::Output),
                kind: fhir::AssocItemConstraintKind::Equality { term: output },
            }]),
        );
        let bound = fhir::GenericBound::Trait(
            fhir::PolyTraitRef { bound_generic_params: &[], trait_ref, span: trait_ref.span },
            fhir::TraitBoundModifier::None,
        );
        let opaque_ty = fhir::OpaqueTy { bounds: self.genv.alloc_slice(&[bound]) };

        Ok(fhir::Item { generics, kind: fhir::ItemKind::OpaqueTy(opaque_ty), owner_id: self.owner })
    }

    fn make_lang_item_path(
        &mut self,
        lang_item: hir::LangItem,
        span: Span,
        args: &'genv [fhir::GenericArg<'genv>],
        constraints: &'genv [fhir::AssocItemConstraint<'genv>],
    ) -> fhir::Path<'genv> {
        let def_id = self.genv.tcx().require_lang_item(lang_item, Some(span));
        let def_kind = self.genv.def_kind(def_id);
        let res = Res::Def(def_kind, def_id);
        fhir::Path {
            span,
            res,
            segments: self.genv.alloc_slice_fill_iter([fhir::PathSegment {
                ident: surface::Ident::new(lang_item.name(), span),
                res,
                args,
                constraints,
            }]),
            refine: &[],
        }
    }

    fn desugar_fn_ret_ty(&mut self, returns: &surface::FnRetTy) -> Result<fhir::Ty<'genv>> {
        match returns {
            surface::FnRetTy::Ty(ty) => self.desugar_ty(ty),
            surface::FnRetTy::Default(span) => {
                let kind = fhir::TyKind::Tuple(&[]);
                Ok(fhir::Ty { kind, span: *span })
            }
        }
    }

    fn desugar_opaque_ty_for_impl_trait(
        &mut self,
        bounds: &[surface::TraitRef],
    ) -> Result<fhir::Item<'genv>> {
        let generics = self.as_lift_cx().lift_generics()?;
        let bounds = self.desugar_generic_bounds(bounds)?;
        let opaque_ty = fhir::OpaqueTy { bounds };
        Ok(fhir::Item { generics, kind: fhir::ItemKind::OpaqueTy(opaque_ty), owner_id: self.owner })
    }

    fn desugar_variant_ret(
        &mut self,
        ret: &surface::VariantRet,
    ) -> Result<fhir::VariantRet<'genv>> {
        let Some(enum_id) = self.check_variant_ret_path(&ret.path) else {
            return Err(self.emit_err(errors::InvalidVariantRet::new(&ret.path)));
        };
        let idx = self.desugar_indices(&ret.indices)?;
        Ok(fhir::VariantRet { enum_id, idx })
    }

    fn check_variant_ret_path(&mut self, path: &surface::Path) -> Option<DefId> {
        let resolved_id = self.owner.resolved_id();

        match self.resolver_output().path_res_map[&path.node_id].full_res()? {
            fhir::Res::Def(DefKind::Enum, def_id) if def_id == resolved_id => {}
            fhir::Res::SelfTyAlias { .. } => return Some(resolved_id),
            _ => return None,
        }

        let generics = self.genv.tcx().generics_of(resolved_id);
        let args = &path.last().args;
        if generics.own_counts().types != args.len() {
            return None;
        }
        let mut i = 0;
        for param in &generics.own_params {
            let rustc_middle::ty::GenericParamDefKind::Type { .. } = param.kind else { continue };
            let arg = &args[i];
            if let surface::GenericArgKind::Type(arg_ty) = &arg.kind
                && let surface::TyKind::Base(arg_bty) = &arg_ty.kind
                && let surface::BaseTyKind::Path(None, arg_path) = &arg_bty.kind
                && let fhir::Res::Def(DefKind::TyParam, def_id) =
                    self.resolver_output().path_res_map[&arg_path.node_id].full_res()?
                && def_id == param.def_id
            {
            } else {
                return None;
            }
            i += 1;
        }

        Some(resolved_id)
    }

    fn insert_opaque_ty(&mut self, def_id: LocalDefId, opaque_ty: fhir::Item<'genv>) {
        self.opaque_tys
            .as_mut()
            .unwrap_or_else(|| bug!("`impl Trait` not supported in this item {def_id:?}"))
            .insert(def_id, opaque_ty);
    }

    #[track_caller]
    fn emit_err<'b>(&'b self, err: impl Diagnostic<'b>) -> ErrorGuaranteed {
        self.sess().emit_err(err)
    }
}

impl<'genv, 'tcx> FluxItemCtxt<'genv, 'tcx> {
    fn new(
        genv: GlobalEnv<'genv, 'tcx>,
        resolver_output: &'genv ResolverOutput,
        owner: Symbol,
    ) -> Self {
        Self { genv, resolver_output, local_id_gen: Default::default(), owner }
    }
}

trait DesugarCtxt<'genv, 'tcx: 'genv> {
    fn genv(&self) -> GlobalEnv<'genv, 'tcx>;
    fn resolver_output(&self) -> &'genv ResolverOutput;
    fn next_fhir_id(&self) -> FhirId;
    fn desugar_impl_trait(
        &mut self,
        node_id: NodeId,
        bounds: &[surface::TraitRef],
    ) -> Result<fhir::TyKind<'genv>>;

    fn sess(&self) -> &'genv FluxSession {
        self.genv().sess()
    }

    fn resolve_implicit_param(&self, node_id: NodeId) -> Option<(fhir::ParamId, fhir::ParamKind)> {
        self.resolver_output().param_res_map.get(&node_id).copied()
    }

    fn desugar_var(&self, path: &surface::ExprPath) -> Result<fhir::ExprKind<'genv>> {
        let res = *self
            .resolver_output()
            .expr_path_res_map
            .get(&path.node_id)
            .unwrap_or_else(|| span_bug!(path.span, "unresolved expr path"));

        if let ExprRes::GlobalFunc(..) = res {
            let span = path.span;
            return Err(self.emit_err(errors::InvalidFuncAsVar { span }));
        }

        let path = fhir::PathExpr {
            segments: self
                .genv()
                .alloc_slice_fill_iter(path.segments.iter().map(|s| s.ident)),
            res,
            fhir_id: self.next_fhir_id(),
            span: path.span,
        };
        Ok(fhir::ExprKind::Var(path, None))
    }

    #[track_caller]
    fn desugar_loc(&self, ident: surface::Ident, node_id: NodeId) -> Result<ExprRes> {
        let res = self.resolver_output().expr_path_res_map[&node_id];
        if let ExprRes::Param(fhir::ParamKind::Loc, _) = res {
            Ok(res)
        } else {
            let span = ident.span;
            Err(self.emit_err(errors::InvalidLoc { span }))
        }
    }

    #[track_caller]
    fn desugar_func(&self, func: surface::Ident, node_id: NodeId) -> Result<fhir::PathExpr<'genv>> {
        let res = self.resolver_output().expr_path_res_map[&node_id];
        if let ExprRes::Param(..) | ExprRes::GlobalFunc(..) = res {
            let segments = self.genv().alloc_slice(&[func]);
            Ok(fhir::PathExpr { segments, res, fhir_id: self.next_fhir_id(), span: func.span })
        } else {
            let span = func.span;
            Err(self.emit_err(errors::InvalidFunc { span }))
        }
    }

    #[track_caller]
    fn resolve_param(&self, node_id: NodeId) -> (fhir::ParamId, fhir::ParamKind) {
        self.resolver_output().param_res_map[&node_id]
    }

    fn resolve_implicit_params(
        &self,
        scope: NodeId,
    ) -> impl ExactSizeIterator<Item = (surface::Ident, fhir::ParamId, fhir::ParamKind)> {
        self.resolver_output()
            .implicit_params
            .get(&scope)
            .map_or(&[][..], |it| it)
            .iter()
            .map(|(ident, param_id)| {
                let (param_id, kind) = self.resolve_param(*param_id);
                (*ident, param_id, kind)
            })
    }

    fn implicit_params_to_params(
        &self,
        scope: NodeId,
    ) -> impl ExactSizeIterator<Item = fhir::RefineParam<'genv>> {
        self.resolve_implicit_params(scope)
            .map(|(ident, id, kind)| {
                let sort = if kind.is_loc() { fhir::Sort::Loc } else { fhir::Sort::Infer };
                fhir::RefineParam {
                    id,
                    name: ident.name,
                    span: ident.span,
                    kind,
                    sort,
                    fhir_id: self.next_fhir_id(),
                }
            })
    }

    fn implicit_params_to_args(&self, scope: NodeId) -> &'genv [fhir::RefineArg<'genv>] {
        self.genv()
            .alloc_slice_fill_iter(
                self.resolve_implicit_params(scope)
                    .map(|(ident, id, kind)| {
                        let span = ident.span;
                        let path = fhir::PathExpr {
                            segments: self.genv().alloc_slice(&[ident]),
                            res: ExprRes::Param(kind, id),
                            fhir_id: self.next_fhir_id(),
                            span: ident.span,
                        };
                        fhir::RefineArg {
                            kind: fhir::RefineArgKind::Expr(fhir::Expr {
                                kind: fhir::ExprKind::Var(path, Some(kind)),
                                fhir_id: self.next_fhir_id(),
                                span,
                            }),
                            fhir_id: self.next_fhir_id(),
                            span,
                        }
                    }),
            )
    }

    fn desugar_refine_params(
        &self,
        params: &[surface::RefineParam],
    ) -> &'genv [fhir::RefineParam<'genv>] {
        self.genv()
            .alloc_slice_fill_iter(self.desugar_refine_params_iter(params))
    }

    fn desugar_refine_params_iter(
        &self,
        params: &[surface::RefineParam],
    ) -> impl ExactSizeIterator<Item = fhir::RefineParam<'genv>> {
        params.iter().map(|param| {
            let (id, kind) = self.resolve_param(param.node_id);
            fhir::RefineParam {
                id,
                name: param.ident.name,
                span: param.ident.span,
                kind,
                sort: self.desugar_sort(&param.sort, None),
                fhir_id: self.next_fhir_id(),
            }
        })
    }

    fn desugar_sort(
        &self,
        sort: &surface::Sort,
        generic_id_to_var_idx: Option<&FxIndexSet<DefId>>,
    ) -> fhir::Sort<'genv> {
        desugar_sort(self.genv(), self.resolver_output(), sort, generic_id_to_var_idx)
    }

    fn desugar_base_sort(
        &self,
        sort: &surface::BaseSort,
        generic_id_to_var_idx: Option<&FxIndexSet<DefId>>,
    ) -> fhir::Sort<'genv> {
        desugar_base_sort(self.genv(), self.resolver_output(), sort, generic_id_to_var_idx)
    }

    fn desugar_generic_args(
        &mut self,
        res: Res,
        args: &[surface::GenericArg],
    ) -> Result<(&'genv [fhir::GenericArg<'genv>], &'genv [fhir::AssocItemConstraint<'genv>])> {
        let mut fhir_args = vec![];
        let mut constraints = vec![];
        if let Res::Def(
            DefKind::TyAlias { .. } | DefKind::Struct | DefKind::Enum | DefKind::OpaqueTy,
            def_id,
        ) = res
        {
            let generics = self.genv().tcx().generics_of(def_id);
            for param in &generics.own_params {
                if let rustc_middle::ty::GenericParamDefKind::Lifetime = param.kind {
                    fhir_args.push(fhir::GenericArg::Lifetime(self.mk_lft_hole()));
                }
            }
        }
        for arg in args {
            match &arg.kind {
                surface::GenericArgKind::Type(ty) => {
                    let ty = self.desugar_ty(ty)?;
                    fhir_args.push(fhir::GenericArg::Type(self.genv().alloc(ty)));
                }
                surface::GenericArgKind::Constraint(ident, ty) => {
                    constraints.push(fhir::AssocItemConstraint {
                        ident: *ident,
                        kind: fhir::AssocItemConstraintKind::Equality {
                            term: self.desugar_ty(ty)?,
                        },
                    });
                }
            }
        }
        Ok((self.genv().alloc_slice(&fhir_args), self.genv().alloc_slice(&constraints)))
    }

    fn desugar_ty(&mut self, ty: &surface::Ty) -> Result<fhir::Ty<'genv>> {
        let node_id = ty.node_id;
        let span = ty.span;
        let kind = match &ty.kind {
            surface::TyKind::Base(bty) => {
                let bty = self.desugar_bty(bty)?;
                fhir::TyKind::BaseTy(bty)
            }
            surface::TyKind::Indexed { bty, indices } => {
                let bty = self.desugar_bty(bty)?;
                let idx = self.desugar_indices(indices)?;
                fhir::TyKind::Indexed(bty, idx)
            }
            surface::TyKind::Exists { bind, bty, pred } => {
                let ty_span = ty.span;
                let bty_span = bty.span;

                let bty = self.desugar_bty(bty)?;
                let pred = self.desugar_expr(pred)?;

                let (id, kind) = self.resolve_param(node_id);
                let param = fhir::RefineParam {
                    id,
                    name: bind.name,
                    span: bind.span,
                    sort: fhir::Sort::Infer,
                    kind,
                    fhir_id: self.next_fhir_id(),
                };
                let path = fhir::PathExpr {
                    segments: self.genv().alloc_slice(&[*bind]),
                    res: ExprRes::Param(kind, id),
                    fhir_id: self.next_fhir_id(),
                    span: bind.span,
                };
                let idx = fhir::RefineArg {
                    kind: fhir::RefineArgKind::Expr(fhir::Expr {
                        kind: fhir::ExprKind::Var(path, None),
                        span: bind.span,
                        fhir_id: self.next_fhir_id(),
                    }),
                    span: bind.span,
                    fhir_id: self.next_fhir_id(),
                };
                let indexed = fhir::Ty { kind: fhir::TyKind::Indexed(bty, idx), span: bty_span };
                let constr = fhir::Ty {
                    kind: fhir::TyKind::Constr(pred, self.genv().alloc(indexed)),
                    span: ty_span,
                };
                fhir::TyKind::Exists(self.genv().alloc_slice(&[param]), self.genv().alloc(constr))
            }
            surface::TyKind::GeneralExists { params, ty, pred } => {
                let mut ty = self.desugar_ty(ty)?;
                if let Some(pred) = pred {
                    let pred = self.desugar_expr(pred)?;
                    ty = fhir::Ty { kind: fhir::TyKind::Constr(pred, self.genv().alloc(ty)), span };
                }
                let params = self.desugar_refine_params(params);

                fhir::TyKind::Exists(params, self.genv().alloc(ty))
            }
            surface::TyKind::Constr(pred, ty) => {
                let pred = self.desugar_expr(pred)?;
                let ty = self.desugar_ty(ty)?;
                fhir::TyKind::Constr(pred, self.genv().alloc(ty))
            }
            surface::TyKind::Ref(mutbl, ty) => {
                let ty = self.desugar_ty(ty)?;
                let mut_ty = fhir::MutTy { ty: self.genv().alloc(ty), mutbl: *mutbl };
                fhir::TyKind::Ref(self.mk_lft_hole(), mut_ty)
            }
            surface::TyKind::Tuple(tys) => {
                let tys = try_alloc_slice!(self.genv(), tys, |ty| self.desugar_ty(ty))?;
                fhir::TyKind::Tuple(tys)
            }
            surface::TyKind::Array(ty, len) => {
                let ty = self.desugar_ty(ty)?;
                let const_arg =
                    fhir::ConstArg { kind: fhir::ConstArgKind::Lit(len.val), span: len.span };
                fhir::TyKind::Array(self.genv().alloc(ty), const_arg)
            }
            surface::TyKind::ImplTrait(node_id, bounds) => {
                self.desugar_impl_trait(*node_id, bounds)?
            }
            surface::TyKind::Hole => fhir::TyKind::Infer,
        };
        Ok(fhir::Ty { kind, span })
    }

    fn desugar_bty(&mut self, bty: &surface::BaseTy) -> Result<fhir::BaseTy<'genv>> {
        match &bty.kind {
            surface::BaseTyKind::Path(qself, path) => {
                let qpath = self.desugar_qpath(qself.as_deref(), path)?;
                Ok(fhir::BaseTy::from_qpath(qpath, self.next_fhir_id()))
            }
            surface::BaseTyKind::Slice(ty) => {
                let ty = self.desugar_ty(ty)?;
                let kind = fhir::BaseTyKind::Slice(self.genv().alloc(ty));
                Ok(fhir::BaseTy { kind, fhir_id: self.next_fhir_id(), span: bty.span })
            }
        }
    }

    fn desugar_path_to_bty(
        &mut self,
        qself: Option<&surface::Ty>,
        path: &surface::Path,
    ) -> Result<fhir::BaseTy<'genv>> {
        let qpath = self.desugar_qpath(qself, path)?;
        Ok(fhir::BaseTy::from_qpath(qpath, self.next_fhir_id()))
    }

    fn desugar_qpath(
        &mut self,
        qself: Option<&surface::Ty>,
        path: &surface::Path,
    ) -> Result<fhir::QPath<'genv>> {
        let qself = qself
            .map(|ty| {
                let ty = self.desugar_ty(ty)?;
                Ok(self.genv().alloc(ty))
            })
            .transpose()?;
        let partial_res = self.resolver_output().path_res_map[&path.node_id];

        let unresolved_segments = partial_res.unresolved_segments();

        let proj_start = path.segments.len() - unresolved_segments;
        let fhir_path = fhir::Path {
            res: partial_res.base_res(),
            segments: try_alloc_slice!(self.genv(), &path.segments[..proj_start], |segment| {
                self.desugar_path_segment(segment)
            })?,
            refine: try_alloc_slice!(self.genv(), &path.refine, |arg| {
                self.desugar_refine_arg(arg)
            })?,
            span: path.span,
        };

        // Simple case, either no projections, or only fully-qualified.
        // E.g., `std::mem::size_of` or `<I as Iterator>::Item`.
        if unresolved_segments == 0 {
            return Ok(fhir::QPath::Resolved(qself, fhir_path));
        }

        // Create the innermost type that we're projecting from.
        let mut ty = if fhir_path.segments.is_empty() {
            // If the base path is empty that means there exists a
            // syntactical `Self`, e.g., `&i32` in `<&i32>::clone`.
            qself.expect("missing QSelf for <T>::...")
        } else {
            // Otherwise, the base path is an implicit `Self` type path,
            // e.g., `Vec` in `Vec::new` or `<I as Iterator>::Item` in
            // `<I as Iterator>::Item::default`.
            self.genv()
                .alloc(self.ty_path(fhir::QPath::Resolved(qself, fhir_path)))
        };

        for (i, segment) in path.segments.iter().enumerate().skip(proj_start) {
            let hir_segment = self.desugar_path_segment(segment)?;
            let qpath = fhir::QPath::TypeRelative(ty, self.genv().alloc(hir_segment));

            if i == path.segments.len() - 1 {
                return Ok(qpath);
            }

            ty = self.genv().alloc(self.ty_path(qpath));
        }

        span_bug!(
            path.span,
            "desugar_qpath: no final extension segment in {}..{}",
            proj_start,
            path.segments.len()
        );
    }

    fn desugar_path_segment(
        &mut self,
        segment: &surface::PathSegment,
    ) -> Result<fhir::PathSegment<'genv>> {
        let res = self
            .resolver_output()
            .path_res_map
            .get(&segment.node_id)
            .map_or(Res::Err, |r| r.expect_full_res());
        let (args, constraints) = self.desugar_generic_args(res, &segment.args)?;
        Ok(fhir::PathSegment { ident: segment.ident, res, args, constraints })
    }

    fn ty_path(&self, qpath: fhir::QPath<'genv>) -> fhir::Ty<'genv> {
        fhir::Ty {
            span: qpath.span(),
            kind: fhir::TyKind::BaseTy(fhir::BaseTy::from_qpath(qpath, self.next_fhir_id())),
        }
    }

    fn mk_lft_hole(&self) -> fhir::Lifetime {
        fhir::Lifetime::Hole(self.next_fhir_id())
    }

    fn desugar_indices(&mut self, idxs: &surface::Indices) -> Result<fhir::RefineArg<'genv>> {
        if let [arg] = &idxs.indices[..] {
            self.desugar_refine_arg(arg)
        } else {
            let flds = try_alloc_slice!(self.genv(), &idxs.indices, |arg| {
                self.desugar_refine_arg(arg)
            })?;
            Ok(fhir::RefineArg {
                kind: fhir::RefineArgKind::Record(flds),
                fhir_id: self.next_fhir_id(),
                span: idxs.span,
            })
        }
    }

    fn desugar_refine_arg(&mut self, arg: &surface::RefineArg) -> Result<fhir::RefineArg<'genv>> {
        match arg {
            surface::RefineArg::Bind(ident, .., node_id) => {
                Ok(self
                    .implicit_param_into_refine_arg(*ident, *node_id)
                    .unwrap())
            }
            surface::RefineArg::Expr(expr) => {
                Ok(fhir::RefineArg {
                    kind: fhir::RefineArgKind::Expr(self.desugar_expr(expr)?),
                    fhir_id: self.next_fhir_id(),
                    span: expr.span,
                })
            }
            surface::RefineArg::Abs(params, body, span, _) => {
                let body = self.desugar_expr(body)?;
                let params = self.desugar_refine_params(params);
                Ok(fhir::RefineArg {
                    kind: fhir::RefineArgKind::Abs(params, body),
                    fhir_id: self.next_fhir_id(),
                    span: *span,
                })
            }
        }
    }

    fn implicit_param_into_refine_arg(
        &self,
        ident: surface::Ident,
        node_id: NodeId,
    ) -> Option<fhir::RefineArg<'genv>> {
        let (id, kind) = self.resolve_implicit_param(node_id)?;
        let path = fhir::PathExpr {
            segments: self.genv().alloc_slice(&[ident]),
            res: ExprRes::Param(kind, id),
            fhir_id: self.next_fhir_id(),
            span: ident.span,
        };
        Some(fhir::RefineArg {
            kind: fhir::RefineArgKind::Expr(fhir::Expr {
                kind: fhir::ExprKind::Var(path, Some(kind)),
                span: ident.span,
                fhir_id: self.next_fhir_id(),
            }),
            fhir_id: self.next_fhir_id(),
            span: ident.span,
        })
    }

    fn desugar_alias_reft(
        &mut self,
        alias_reft: &surface::AliasReft,
    ) -> Result<fhir::AliasReft<'genv>> {
        let self_ty = self.desugar_ty(&alias_reft.qself)?;
        let fhir::QPath::Resolved(None, path) = self.desugar_qpath(None, &alias_reft.path)? else {
            span_bug!(alias_reft.path.span, "desugar_alias_reft: unexpected qpath")
        };
        if let Res::Def(DefKind::Trait, _) = path.res {
            Ok(fhir::AliasReft {
                qself: self.genv().alloc(self_ty),
                path,
                name: alias_reft.name.name,
            })
        } else {
            // FIXME(nilehmann) we ought to report this error somewhere else
            Err(self.emit_err(errors::InvalidAliasReft::new(&alias_reft.path)))
        }
    }

    fn desugar_expr(&mut self, expr: &surface::Expr) -> Result<fhir::Expr<'genv>> {
        let node_id = expr.node_id;
        let kind = match &expr.kind {
            surface::ExprKind::Path(path) => self.desugar_var(path)?,
            surface::ExprKind::Literal(lit) => {
                fhir::ExprKind::Literal(self.desugar_lit(expr.span, *lit)?)
            }
            surface::ExprKind::BinaryOp(op, box [e1, e2]) => {
                let e1 = self.desugar_expr(e1);
                let e2 = self.desugar_expr(e2);
                fhir::ExprKind::BinaryOp(*op, self.genv().alloc(e1?), self.genv().alloc(e2?))
            }
            surface::ExprKind::UnaryOp(op, box e) => {
                fhir::ExprKind::UnaryOp(*op, self.genv().alloc(self.desugar_expr(e)?))
            }
            surface::ExprKind::Dot(path, fld) => {
                let res = self.resolver_output().expr_path_res_map[&path.node_id];
                if let ExprRes::Param(..) = res {
                    let segments = self
                        .genv()
                        .alloc_slice_fill_iter(path.segments.iter().map(|s| s.ident));
                    let path = fhir::PathExpr {
                        segments,
                        res,
                        fhir_id: self.next_fhir_id(),
                        span: path.span,
                    };
                    fhir::ExprKind::Dot(path, *fld)
                } else {
                    return Err(self.emit_err(errors::InvalidDotVar { span: path.span }));
                }
            }
            surface::ExprKind::App(func, args) => {
                let args = self.desugar_exprs(args)?;
                let func = self.desugar_func(*func, node_id)?;
                fhir::ExprKind::App(func, args)
            }
            surface::ExprKind::Alias(alias_reft, func_args) => {
                let func_args = try_alloc_slice!(self.genv(), func_args, |e| self.desugar_expr(e))?;
                let alias_reft = self.desugar_alias_reft(alias_reft)?;
                fhir::ExprKind::Alias(alias_reft, func_args)
            }
            surface::ExprKind::IfThenElse(box [p, e1, e2]) => {
                let p = self.desugar_expr(p);
                let e1 = self.desugar_expr(e1);
                let e2 = self.desugar_expr(e2);
                fhir::ExprKind::IfThenElse(
                    self.genv().alloc(p?),
                    self.genv().alloc(e1?),
                    self.genv().alloc(e2?),
                )
            }
        };

        Ok(fhir::Expr { kind, span: expr.span, fhir_id: self.next_fhir_id() })
    }

    fn desugar_exprs(&mut self, exprs: &[surface::Expr]) -> Result<&'genv [fhir::Expr<'genv>]> {
        try_alloc_slice!(self.genv(), exprs, |e| self.desugar_expr(e))
    }

    fn try_parse_int_lit(&self, span: Span, s: &str) -> Result<i128> {
        let s = s.replace("_", "");
        let parsed_int = if s.len() <= 2 {
            s.parse::<i128>()
        } else {
            match &s[0..2] {
                "0x" => i128::from_str_radix(&s[2..], 16), // hex
                "0o" => i128::from_str_radix(&s[2..], 8),  // octal
                "0b" => i128::from_str_radix(&s[2..], 2),  // binary
                _ => s.parse::<i128>(),                    // must be decimal
            }
        };

        if let Ok(n) = parsed_int {
            Ok(n) // convert error types
        } else {
            Err(self.emit_err(errors::IntTooLarge { span }))
        }
    }

    fn desugar_lit(&self, span: Span, lit: surface::Lit) -> Result<fhir::Lit> {
        match lit.kind {
            surface::LitKind::Integer => {
                let n = self.try_parse_int_lit(span, lit.symbol.as_str())?;
                let suffix = lit.suffix.unwrap_or(SORTS.int);
                if suffix == SORTS.int {
                    Ok(fhir::Lit::Int(n))
                } else if suffix == SORTS.real {
                    Ok(fhir::Lit::Real(n))
                } else {
                    Err(self.emit_err(errors::InvalidNumericSuffix::new(span, suffix)))
                }
            }
            surface::LitKind::Bool => Ok(fhir::Lit::Bool(lit.symbol == kw::True)),
            surface::LitKind::Str => Ok(fhir::Lit::Str(lit.symbol)),
            _ => Err(self.emit_err(errors::UnexpectedLiteral { span })),
        }
    }

    #[track_caller]
    fn emit_err(&self, err: impl Diagnostic<'genv>) -> ErrorGuaranteed {
        self.sess().emit_err(err)
    }
}

fn desugar_sort<'genv>(
    genv: GlobalEnv<'genv, '_>,
    resolver_output: &ResolverOutput,
    sort: &surface::Sort,
    generic_id_to_var_idx: Option<&FxIndexSet<DefId>>,
) -> fhir::Sort<'genv> {
    match sort {
        surface::Sort::Base(bsort) => {
            desugar_base_sort(genv, resolver_output, bsort, generic_id_to_var_idx)
        }
        surface::Sort::Func { inputs, output } => {
            let inputs_and_output = genv.alloc_slice_with_capacity(
                inputs.len() + 1,
                inputs.iter().chain(iter::once(output)).map(|sort| {
                    desugar_base_sort(genv, resolver_output, sort, generic_id_to_var_idx)
                }),
            );
            fhir::Sort::Func(fhir::PolyFuncSort::new(0, inputs_and_output))
        }
        surface::Sort::Infer => fhir::Sort::Infer,
    }
}

fn desugar_base_sort<'genv>(
    genv: GlobalEnv<'genv, '_>,
    resolver_output: &ResolverOutput,
    bsort: &surface::BaseSort,
    generic_id_to_var_idx: Option<&FxIndexSet<DefId>>,
) -> fhir::Sort<'genv> {
    match bsort {
        surface::BaseSort::BitVec(width) => fhir::Sort::BitVec(*width),
        surface::BaseSort::Path(surface::SortPath { segments, args, node_id }) => {
            let res = resolver_output.sort_path_res_map[node_id];

            // In a `RefinedBy` we resolve type parameters to a sort var
            let res = if let fhir::SortRes::TyParam(def_id) = res
                && let Some(generic_id_to_var_idx) = generic_id_to_var_idx
            {
                let idx = generic_id_to_var_idx.get_index_of(&def_id).unwrap();
                fhir::SortRes::SortParam(idx)
            } else {
                res
            };

            let args = genv.alloc_slice_fill_iter(
                args.iter()
                    .map(|s| desugar_base_sort(genv, resolver_output, s, generic_id_to_var_idx)),
            );

            let path = fhir::SortPath { res, segments: genv.alloc_slice(segments), args };
            fhir::Sort::Path(path)
        }
    }
}

impl<'a, 'genv, 'tcx> DesugarCtxt<'genv, 'tcx> for RustItemCtxt<'a, 'genv, 'tcx> {
    fn next_fhir_id(&self) -> FhirId {
        FhirId {
            owner: FluxOwnerId::Rust(self.owner.local_id()),
            local_id: self.local_id_gen.fresh(),
        }
    }

    fn genv(&self) -> GlobalEnv<'genv, 'tcx> {
        self.genv
    }

    fn resolver_output(&self) -> &'genv ResolverOutput {
        self.resolver_output
    }

    fn desugar_impl_trait(
        &mut self,
        node_id: NodeId,
        bounds: &[surface::TraitRef],
    ) -> Result<fhir::TyKind<'genv>> {
        let item_id = self.resolver_output().impl_trait_res_map[&node_id];
        let def_id = item_id.owner_id.def_id;
        let res = Res::Def(DefKind::OpaqueTy, def_id.to_def_id());

        // FIXME(nilehmann) since we can only pass local ids for opaque types it means we can't
        // support extern specs with opaque types.
        let opaque_ty = self
            .with_new_owner(MaybeExternId::Local(item_id.owner_id))
            .desugar_opaque_ty_for_impl_trait(bounds)?;
        self.insert_opaque_ty(def_id, opaque_ty);

        let (args, _) = self.desugar_generic_args(res, &[])?;
        let refine_args = self.implicit_params_to_args(self.fn_sig_scope.unwrap());
        Ok(fhir::TyKind::OpaqueDef(item_id, args, refine_args, false))
    }
}

impl<'genv, 'tcx> DesugarCtxt<'genv, 'tcx> for FluxItemCtxt<'genv, 'tcx> {
    fn next_fhir_id(&self) -> FhirId {
        FhirId { owner: FluxOwnerId::Flux(self.owner), local_id: self.local_id_gen.fresh() }
    }

    fn genv(&self) -> GlobalEnv<'genv, 'tcx> {
        self.genv
    }

    fn resolver_output(&self) -> &'genv ResolverOutput {
        self.resolver_output
    }

    fn desugar_impl_trait(
        &mut self,
        _: NodeId,
        _: &[surface::TraitRef],
    ) -> Result<fhir::TyKind<'genv>> {
        unimplemented!("`impl Trait` not supported in this item")
    }
}
