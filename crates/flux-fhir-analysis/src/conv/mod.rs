//! Conversion from types in [`fhir`] to types in [`rty`]
//!
//! Conversion assumes well-formedness and will panic if type are not well-formed. Among other things,
//! well-formedness implies:
//! 1. Names are bound correctly.
//! 2. Refinement parameters appear in allowed positions. This is particularly important for
//!    refinement predicates, aka abstract refinements, since the syntax in [`rty`] has
//!    syntactic restrictions on predicates.
//! 3. Refinements are well-sorted.

mod struct_compat;
use std::{borrow::Borrow, iter};

use flux_common::{bug, iter::IterExt, span_bug};
use flux_middle::{
    fhir::{self, ExprRes, FhirId, FluxOwnerId},
    global_env::GlobalEnv,
    queries::QueryResult,
    query_bug,
    rty::{
        self,
        fold::TypeFoldable,
        refining::{self, Refiner},
        AdtSortDef, ESpan, List, WfckResults, INNERMOST,
    },
    MaybeExternId,
};
use flux_rustc_bridge::ToRustc;
use itertools::Itertools;
use rustc_data_structures::fx::FxIndexMap;
use rustc_errors::Diagnostic;
use rustc_hash::FxHashSet;
use rustc_hir::{
    self as hir,
    def::DefKind,
    def_id::{DefId, LocalDefId},
    PrimTy, Safety,
};
use rustc_middle::{
    middle::resolve_bound_vars::ResolvedArg,
    ty::{self, AssocItem, AssocKind, BoundRegionKind::BrNamed, BoundVar},
};
use rustc_span::{
    symbol::{kw, Ident},
    ErrorGuaranteed, Span, Symbol, DUMMY_SP,
};
use rustc_target::spec::abi;
use rustc_trait_selection::traits;
use rustc_type_ir::DebruijnIndex;

pub struct ConvCtxt<'a, 'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    wfckresults: &'a WfckResults,
    next_type_index: u32,
    next_region_index: u32,
    next_const_index: u32,
}

pub(crate) struct Env {
    layers: Vec<Layer>,
    early_bound: FxIndexMap<fhir::ParamId, (Symbol, rty::Sort)>,
}

#[derive(Debug, Clone)]
struct Layer {
    map: FxIndexMap<fhir::ParamId, ParamEntry>,
    kind: LayerKind,
}

/// Whether the list of parameters in a layer is converted into a list of bound variables or
/// coalesced into a single parameter of [adt] sort.
///
/// [adt]: rty::SortCtor::Adt
#[derive(Debug, Clone, Copy)]
enum LayerKind {
    List {
        /// The number of regions bound in this layer. Since regions and refinements are both
        /// bound with a [`rty::Binder`] we need to keep track of the number of bound regions
        /// to skip them when assigning an index to refinement parameters.
        bound_regions: u32,
    },
    Coalesce(DefId),
}

#[derive(Debug, Clone)]
struct ParamEntry {
    name: Symbol,
    sort: rty::Sort,
    mode: rty::InferMode,
}

#[derive(Debug)]
struct LookupResult<'a> {
    kind: LookupResultKind<'a>,
    /// The span of the variable that originated the lookup.
    var_span: Span,
}

#[derive(Debug)]
enum LookupResultKind<'a> {
    LateBound {
        debruijn: DebruijnIndex,
        entry: &'a ParamEntry,
        kind: LayerKind,
        /// The index of the parameter in the layer.
        index: u32,
    },
    EarlyParam {
        name: Symbol,
        sort: rty::Sort,
        /// The index of the parameter.
        index: u32,
    },
}

pub(crate) fn conv_adt_sort_def(
    genv: GlobalEnv,
    def_id: LocalDefId,
    refined_by: &fhir::RefinedBy,
) -> QueryResult<rty::AdtSortDef> {
    let params = refined_by
        .sort_params
        .iter()
        .map(|def_id| def_id_to_param_ty(genv, *def_id))
        .collect();
    let fields = refined_by
        .fields
        .iter()
        .map(|(name, sort)| -> QueryResult<_> {
            Ok((*name, conv_sort(genv, sort, &mut bug_on_infer_sort)?))
        })
        .try_collect_vec()?;
    let def_id = genv.resolve_maybe_extern_id(def_id.to_def_id());
    Ok(rty::AdtSortDef::new(def_id, params, fields))
}

pub(crate) fn expand_type_alias(
    genv: GlobalEnv,
    def_id: MaybeExternId,
    alias: &fhir::TyAlias,
    wfckresults: &WfckResults,
) -> QueryResult<rty::Binder<rty::Ty>> {
    let mut cx = ConvCtxt::new(genv, wfckresults);
    let generics = genv.map().get_generics(def_id.local_id())?.unwrap();

    let mut env = Env::new(genv, generics.refinement_params, wfckresults)?;
    env.push_layer(Layer::coalesce(&cx, def_id.resolved_id(), alias.params)?);

    let ty = cx.conv_ty(&mut env, &alias.ty)?;

    let ty = struct_compat::type_alias(genv, alias, &ty, def_id)?;

    Ok(rty::Binder::new(ty, env.pop_layer().into_bound_vars(genv)?))
}

pub(crate) fn conv_generic_predicates(
    genv: GlobalEnv,
    def_id: LocalDefId,
    predicates: &[fhir::WhereBoundPredicate],
    wfckresults: &WfckResults,
) -> QueryResult<rty::EarlyBinder<rty::GenericPredicates>> {
    let mut cx = ConvCtxt::new(genv, wfckresults);

    let refparams = &genv.map().get_generics(def_id)?.unwrap().refinement_params;

    let env = &mut Env::new(genv, refparams, wfckresults)?;

    let mut clauses = vec![];
    for pred in predicates {
        let span = pred.bounded_ty.span;
        let bounded_ty = cx.conv_ty(env, &pred.bounded_ty)?;
        for clause in cx.conv_generic_bounds(env, span, bounded_ty, pred.bounds)? {
            clauses.push(clause);
        }
    }
    let parent = genv.tcx().predicates_of(def_id.to_def_id()).parent;
    Ok(rty::EarlyBinder(rty::GenericPredicates { parent, predicates: List::from_vec(clauses) }))
}

pub(crate) fn conv_opaque_ty(
    genv: GlobalEnv,
    def_id: LocalDefId,
    opaque_ty: &fhir::OpaqueTy,
    wfckresults: &WfckResults,
) -> QueryResult<rty::Clauses> {
    let mut cx = ConvCtxt::new(genv, wfckresults);
    let parent = genv.tcx().local_parent(def_id);
    let refparams = &genv.map().get_generics(parent)?.unwrap().refinement_params;
    let parent_wfckresults = genv.check_wf(parent)?;

    let env = &mut Env::new(genv, refparams, &parent_wfckresults)?;

    let args = rty::GenericArg::identity_for_item(genv, def_id)?;
    let self_ty = rty::Ty::opaque(def_id, args, env.to_early_bound_vars());
    // FIXME(nilehmann) use a good span here
    Ok(cx
        .conv_generic_bounds(env, DUMMY_SP, self_ty, opaque_ty.bounds)?
        .into_iter()
        .collect())
}

pub(crate) fn conv_generics(
    genv: GlobalEnv,
    generics: &fhir::Generics,
    def_id: MaybeExternId,
    is_trait: bool,
) -> QueryResult<rty::Generics> {
    let opt_self = is_trait.then(|| {
        let kind = generics
            .self_kind
            .as_ref()
            .map_or(rty::GenericParamDefKind::Type { has_default: false }, conv_generic_param_kind);
        rty::GenericParamDef { index: 0, name: kw::SelfUpper, def_id: def_id.resolved_id(), kind }
    });
    let rust_generics = genv.tcx().generics_of(def_id.local_id());
    let mut params = opt_self
        .into_iter()
        .chain(rust_generics.own_params.iter().flat_map(|rust_param| {
            // We have to filter out late bound parameters
            let param = generics
                .params
                .iter()
                .find(|param| param.def_id.to_def_id() == rust_param.def_id)?;
            let def_id = param.def_id.to_def_id();
            Some(rty::GenericParamDef {
                kind: conv_generic_param_kind(&param.kind),
                def_id,
                index: rust_param.index,
                name: rust_param.name,
            })
        }))
        .collect_vec();

    // HACK(nilehmann) add host param for effect to std/core external specs
    if let Some(extern_id) = def_id.as_extern() {
        if let Some((pos, param)) = genv
            .lower_generics_of(extern_id)
            .params
            .iter()
            .find_position(|p| p.is_host_effect())
        {
            params.insert(
                pos,
                rty::GenericParamDef {
                    kind: refining::refine_generic_param_def_kind(param.kind),
                    def_id: param.def_id,
                    index: param.index,
                    name: param.name,
                },
            );
        }
    }

    Ok(rty::Generics {
        own_params: List::from_vec(params),
        parent: rust_generics.parent,
        parent_count: rust_generics.parent_count,
        has_self: rust_generics.has_self,
    })
}

pub(crate) fn conv_refinement_generics(
    genv: GlobalEnv,
    params: &[fhir::RefineParam],
    wfckresults: Option<&WfckResults>,
) -> QueryResult<List<rty::RefineParam>> {
    params
        .iter()
        .map(|param| {
            let sort = resolve_param_sort(genv, param, wfckresults)?;
            let mode = rty::InferMode::from_param_kind(param.kind);
            Ok(rty::RefineParam { sort, name: param.name, mode })
        })
        .try_collect()
}

fn conv_generic_param_kind(kind: &fhir::GenericParamKind) -> rty::GenericParamDefKind {
    match kind {
        fhir::GenericParamKind::Type { default } => {
            rty::GenericParamDefKind::Type { has_default: default.is_some() }
        }
        fhir::GenericParamKind::Base => rty::GenericParamDefKind::Base,
        fhir::GenericParamKind::Lifetime => rty::GenericParamDefKind::Lifetime,
        fhir::GenericParamKind::Const { is_host_effect: _, .. } => {
            rty::GenericParamDefKind::Const { has_default: false }
        }
    }
}

pub(crate) fn conv_invariants(
    genv: GlobalEnv,
    def_id: MaybeExternId,
    params: &[fhir::RefineParam],
    invariants: &[fhir::Expr],
    wfckresults: &WfckResults,
) -> QueryResult<Vec<rty::Invariant>> {
    let mut cx = ConvCtxt::new(genv, wfckresults);
    let mut env = Env::new(genv, &[], wfckresults)?;
    env.push_layer(Layer::coalesce(&cx, def_id.resolved_id(), params)?);
    cx.conv_invariants(&mut env, invariants)
}

pub(crate) fn conv_defn(
    genv: GlobalEnv,
    func: &fhir::SpecFunc,
    wfckresults: &WfckResults,
) -> QueryResult<Option<rty::SpecFunc>> {
    if let Some(body) = &func.body {
        let mut cx = ConvCtxt::new(genv, wfckresults);
        let mut env = Env::new(genv, &[], wfckresults)?;
        env.push_layer(Layer::list(&cx, 0, func.args)?);
        let expr = cx.conv_expr(&mut env, body)?;
        let expr = rty::Binder::new(expr, env.pop_layer().into_bound_vars(genv)?);
        Ok(Some(rty::SpecFunc { name: func.name, expr }))
    } else {
        Ok(None)
    }
}

pub(crate) fn conv_qualifier(
    genv: GlobalEnv,
    qualifier: &fhir::Qualifier,
    wfckresults: &WfckResults,
) -> QueryResult<rty::Qualifier> {
    let mut cx = ConvCtxt::new(genv, wfckresults);
    let mut env = Env::new(genv, &[], wfckresults)?;
    env.push_layer(Layer::list(&cx, 0, qualifier.args)?);
    let body = cx.conv_expr(&mut env, &qualifier.expr)?;
    let body = rty::Binder::new(body, env.pop_layer().into_bound_vars(genv)?);
    Ok(rty::Qualifier { name: qualifier.name, body, global: qualifier.global })
}

pub(crate) fn conv_fn_sig(
    genv: GlobalEnv,
    def_id: MaybeExternId,
    fn_sig: &fhir::FnSig,
    wfckresults: &WfckResults,
) -> QueryResult<rty::EarlyBinder<rty::PolyFnSig>> {
    let decl = &fn_sig.decl;
    let header = fn_sig.header;

    let mut cx = ConvCtxt::new(genv, wfckresults);

    let late_bound_regions =
        refining::refine_bound_variables(&genv.lower_late_bound_vars(def_id.local_id())?);

    let generics = genv.map().get_generics(def_id.local_id())?.unwrap();
    let mut env = Env::new(genv, generics.refinement_params, wfckresults)?;
    env.push_layer(Layer::list(&cx, late_bound_regions.len() as u32, &[])?);

    let fn_sig = cx.conv_fn_decl(&mut env, header.safety, header.abi, decl)?;

    let vars = late_bound_regions
        .iter()
        .chain(env.pop_layer().into_bound_vars(genv)?.iter())
        .cloned()
        .collect();

    let poly_fn_sig = rty::PolyFnSig::new(fn_sig, vars);
    let poly_fn_sig = struct_compat::fn_sig(genv, decl, &poly_fn_sig, def_id)?;

    Ok(rty::EarlyBinder(poly_fn_sig))
}

pub(crate) fn conv_default_assoc_reft_def(
    genv: GlobalEnv,
    assoc_reft: &fhir::TraitAssocReft,
    wfckresults: &WfckResults,
) -> QueryResult<Option<rty::Lambda>> {
    if let Some(body) = assoc_reft.body {
        let res =
            conv_assoc_reft_body(genv, wfckresults, assoc_reft.params, &body, &assoc_reft.output)?;
        Ok(Some(res))
    } else {
        Ok(None)
    }
}

pub(crate) fn conv_assoc_reft_def(
    genv: GlobalEnv,
    assoc_reft: &fhir::ImplAssocReft,
    wfckresults: &WfckResults,
) -> QueryResult<rty::Lambda> {
    conv_assoc_reft_body(genv, wfckresults, assoc_reft.params, &assoc_reft.body, &assoc_reft.output)
}

fn conv_assoc_reft_body(
    genv: GlobalEnv,
    wfckresults: &WfckResults,
    params: &[fhir::RefineParam],
    body: &fhir::Expr,
    output: &fhir::Sort,
) -> QueryResult<rty::Lambda> {
    let mut cx = ConvCtxt::new(genv, wfckresults);
    let mut env = Env::new(genv, &[], wfckresults)?;
    env.push_layer(Layer::list(&cx, 0, params)?);
    let expr = cx.conv_expr(&mut env, body)?;
    let inputs = env.pop_layer().into_bound_vars(genv)?;
    let output = conv_sort(genv, output, &mut bug_on_infer_sort)?;
    Ok(rty::Lambda::with_vars(expr, inputs, output))
}

pub(crate) fn conv_ty(
    genv: GlobalEnv,
    ty: &fhir::Ty,
    wfckresults: &WfckResults,
) -> QueryResult<rty::Binder<rty::Ty>> {
    let mut env = Env::new(genv, &[], wfckresults)?;
    let ty = ConvCtxt::new(genv, wfckresults).conv_ty(&mut env, ty)?;
    Ok(rty::Binder::new(ty, List::empty()))
}

impl<'a, 'genv, 'tcx> ConvCtxt<'a, 'genv, 'tcx> {
    pub(crate) fn new(genv: GlobalEnv<'genv, 'tcx>, wfckresults: &'a WfckResults) -> Self {
        Self {
            genv,
            wfckresults,
            // We start from 1 to skip the trait object dummy self type.
            // See [`rty::Ty::trait_object_dummy_self`]
            next_type_index: 1,
            next_region_index: 0,
            next_const_index: 0,
        }
    }

    fn conv_generic_bounds(
        &mut self,
        env: &mut Env,
        bounded_ty_span: Span,
        bounded_ty: rty::Ty,
        bounds: fhir::GenericBounds,
    ) -> QueryResult<Vec<rty::Clause>> {
        let mut clauses = vec![];
        for bound in bounds {
            match bound {
                fhir::GenericBound::Trait(poly_trait_ref, fhir::TraitBoundModifier::None) => {
                    let trait_id = poly_trait_ref.trait_def_id();
                    if let Some(closure_kind) = self.genv.tcx().fn_trait_kind_from_def_id(trait_id)
                    {
                        self.conv_fn_bound(
                            env,
                            &bounded_ty,
                            poly_trait_ref,
                            closure_kind,
                            &mut clauses,
                        )?;
                    } else {
                        self.conv_poly_trait_ref(
                            env,
                            bounded_ty_span,
                            &bounded_ty,
                            poly_trait_ref,
                            &mut clauses,
                        )?;
                    }
                }
                fhir::GenericBound::Outlives(lft) => {
                    let re = self.conv_lifetime(env, *lft);
                    clauses.push(rty::Clause::new(
                        List::empty(),
                        rty::ClauseKind::TypeOutlives(rty::OutlivesPredicate(
                            bounded_ty.clone(),
                            re,
                        )),
                    ));
                }
                // Maybe bounds are only supported for `?Sized`. The effect of the maybe bound is to
                // relax the default which is `Sized` to not have the `Sized` bound, so we just skip
                // it here.
                fhir::GenericBound::Trait(_, fhir::TraitBoundModifier::Maybe) => {}
            }
        }
        Ok(clauses)
    }

    /// Converts a `T: Trait<T0, ..., A0 = S0, ...>` bound
    fn conv_poly_trait_ref(
        &mut self,
        env: &mut Env,
        span: Span,
        bounded_ty: &rty::Ty,
        poly_trait_ref: &fhir::PolyTraitRef,
        clauses: &mut Vec<rty::Clause>,
    ) -> QueryResult {
        let trait_id = poly_trait_ref.trait_def_id();
        let generics = self.genv.generics_of(trait_id)?;
        let trait_segment = poly_trait_ref.trait_ref.last_segment();

        let self_param = generics.param_at(0, self.genv)?;
        let mut args = vec![self.ty_to_generic_arg(self_param.kind, span, bounded_ty)?];
        self.conv_generic_args_into(env, trait_id, trait_segment, &mut args)?;

        let vars = poly_trait_ref
            .bound_generic_params
            .iter()
            .map(|param| self.conv_trait_bound_generic_param(param))
            .try_collect_vec()?;
        let poly_trait_ref = rty::Binder::new(
            rty::TraitRef { def_id: trait_id, args: args.into() },
            List::from_vec(vars),
        );

        clauses.push(
            poly_trait_ref
                .clone()
                .map(|trait_ref| {
                    rty::ClauseKind::Trait(rty::TraitPredicate { trait_ref: trait_ref.clone() })
                })
                .into(),
        );

        for cstr in trait_segment.constraints {
            self.conv_assoc_item_constraint(env, &poly_trait_ref, cstr, clauses)?;
        }

        Ok(())
    }

    fn conv_assoc_item_constraint(
        &mut self,
        env: &mut Env,
        poly_trait_ref: &rty::PolyTraitRef,
        constraint: &fhir::AssocItemConstraint,
        clauses: &mut Vec<rty::Clause>,
    ) -> QueryResult {
        let tcx = self.genv.tcx();

        let candidate = self.probe_single_bound_for_assoc_item(
            || traits::supertraits(tcx, poly_trait_ref.to_rustc(tcx)),
            constraint.ident,
        )?;
        let assoc_item_id = self
            .trait_defines_associated_item_named(
                candidate.def_id(),
                AssocKind::Type,
                constraint.ident,
            )
            .unwrap()
            .def_id;

        let fhir::AssocItemConstraintKind::Equality { term } = &constraint.kind;
        let term = self.conv_ty(env, term)?;

        let clause = poly_trait_ref
            .clone()
            .map(|trait_ref| {
                // TODO: when we support generic associated types, we need to also attach the associated generics here
                let args = trait_ref.args;
                let refine_args = List::empty();
                let projection_ty = rty::AliasTy { def_id: assoc_item_id, args, refine_args };

                rty::ClauseKind::Projection(rty::ProjectionPredicate { projection_ty, term })
            })
            .into();

        clauses.push(clause);
        Ok(())
    }

    fn conv_trait_bound_generic_param(
        &self,
        param: &fhir::GenericParam,
    ) -> QueryResult<rty::BoundVariableKind> {
        match &param.kind {
            fhir::GenericParamKind::Lifetime => {
                let def_id = param.def_id;
                let name = self
                    .genv
                    .tcx()
                    .hir()
                    .name(self.genv.tcx().local_def_id_to_hir_id(def_id));
                let kind = rty::BoundRegionKind::BrNamed(def_id.to_def_id(), name);
                Ok(rty::BoundVariableKind::Region(kind))
            }
            fhir::GenericParamKind::Const { .. }
            | fhir::GenericParamKind::Type { .. }
            | fhir::GenericParamKind::Base => {
                bug!("unexpected!")
            }
        }
    }

    fn conv_fn_bound(
        &mut self,
        env: &mut Env,
        self_ty: &rty::Ty,
        trait_ref: &fhir::PolyTraitRef,
        kind: rty::ClosureKind,
        clauses: &mut Vec<rty::Clause>,
    ) -> QueryResult {
        let path = &trait_ref.trait_ref;
        let layer = Layer::list(self, trait_ref.bound_generic_params.len() as u32, &[])?;
        env.push_layer(layer);

        let fhir::AssocItemConstraintKind::Equality { term } =
            &path.last_segment().constraints[0].kind;

        let pred = rty::FnTraitPredicate {
            self_ty: self_ty.clone(),
            tupled_args: self.conv_ty(env, path.last_segment().args[0].expect_type())?,
            output: self.conv_ty(env, term)?,
            kind,
        };
        // FIXME(nilehmann) We should use `tcx.late_bound_vars` here instead of trusting our lowering
        let vars = trait_ref
            .bound_generic_params
            .iter()
            .map(|param| self.conv_trait_bound_generic_param(param))
            .try_collect_vec()?;
        clauses.push(rty::Clause::new(vars, rty::ClauseKind::FnTrait(pred)));
        Ok(())
    }

    fn trait_defines_associated_item_named(
        &self,
        trait_def_id: DefId,
        assoc_kind: AssocKind,
        assoc_name: Ident,
    ) -> Option<&AssocItem> {
        self.genv
            .tcx()
            .associated_items(trait_def_id)
            .find_by_name_and_kind(self.genv.tcx(), assoc_name, assoc_kind, trait_def_id)
    }

    fn conv_fn_output(
        &mut self,
        env: &mut Env,
        output: &fhir::FnOutput,
    ) -> QueryResult<rty::Binder<rty::FnOutput>> {
        env.push_layer(Layer::list(self, 0, output.params)?);

        let ret = self.conv_ty(env, &output.ret)?;
        let ensures: List<rty::Ensures> = output
            .ensures
            .iter()
            .map(|ens| self.conv_ensures(env, ens))
            .try_collect()?;
        let output = rty::FnOutput::new(ret, ensures);

        let vars = env.pop_layer().into_bound_vars(self.genv)?;
        Ok(rty::Binder::new(output, vars))
    }

    pub(crate) fn conv_enum_variants(
        genv: GlobalEnv,
        adt_def_id: MaybeExternId,
        enum_def: &fhir::EnumDef,
        wfckresults: &WfckResults,
    ) -> QueryResult<Vec<rty::PolyVariant>> {
        let variants = enum_def
            .variants
            .iter()
            .map(|variant_def| {
                ConvCtxt::conv_enum_variant(genv, adt_def_id, variant_def, wfckresults)
            })
            .try_collect_vec()?;
        let variants = struct_compat::variants(genv, &variants, adt_def_id)?;
        Ok(variants)
    }

    fn conv_enum_variant(
        genv: GlobalEnv,
        adt_def_id: MaybeExternId,
        variant: &fhir::VariantDef,
        wfckresults: &WfckResults,
    ) -> QueryResult<rty::PolyVariant> {
        let mut cx = ConvCtxt::new(genv, wfckresults);

        let mut env = Env::new(genv, &[], wfckresults)?;
        env.push_layer(Layer::list(&cx, 0, variant.params)?);

        let fields = variant
            .fields
            .iter()
            .map(|field| cx.conv_ty(&mut env, &field.ty))
            .try_collect()?;

        let adt_def = genv.adt_def(adt_def_id)?;
        let idxs = cx.conv_refine_arg(&mut env, &variant.ret.idx)?;
        let variant = rty::VariantSig::new(
            adt_def,
            rty::GenericArg::identity_for_item(genv, adt_def_id.resolved_id())?,
            fields,
            idxs,
        );

        Ok(rty::Binder::new(variant, env.pop_layer().into_bound_vars(genv)?))
    }

    pub(crate) fn conv_struct_variant(
        genv: GlobalEnv,
        adt_def_id: MaybeExternId,
        struct_def: &fhir::StructDef,
        wfckresults: &WfckResults,
    ) -> QueryResult<rty::Opaqueness<Vec<rty::PolyVariant>>> {
        let mut cx = ConvCtxt::new(genv, wfckresults);
        let mut env = Env::new(genv, &[], wfckresults)?;
        env.push_layer(Layer::list(&cx, 0, struct_def.params)?);

        if let fhir::StructKind::Transparent { fields } = &struct_def.kind {
            let adt_def = genv.adt_def(adt_def_id)?;

            let fields = fields
                .iter()
                .map(|field_def| cx.conv_ty(&mut env, &field_def.ty))
                .try_collect()?;

            let vars = env.pop_layer().into_bound_vars(genv)?;
            let idx = rty::Expr::adt(
                adt_def_id.resolved_id(),
                (0..vars.len())
                    .map(|idx| {
                        rty::Expr::bvar(
                            INNERMOST,
                            BoundVar::from_usize(idx),
                            rty::BoundReftKind::Annon,
                        )
                    })
                    .collect(),
            );
            let variant = rty::VariantSig::new(
                adt_def,
                rty::GenericArg::identity_for_item(genv, adt_def_id.resolved_id())?,
                fields,
                idx,
            );
            let variant = rty::Binder::new(variant, vars);
            let variants = struct_compat::variants(genv, &[variant], adt_def_id)?;
            Ok(rty::Opaqueness::Transparent(variants))
        } else {
            Ok(rty::Opaqueness::Opaque)
        }
    }

    fn conv_fn_decl(
        &mut self,
        env: &mut Env,
        safety: Safety,
        abi: abi::Abi,
        decl: &fhir::FnDecl,
    ) -> QueryResult<rty::FnSig> {
        let mut requires = vec![];
        for req in decl.requires {
            requires.push(self.conv_requires(env, req)?);
        }

        let mut inputs = vec![];
        for ty in decl.inputs {
            inputs.push(self.conv_ty(env, ty)?);
        }

        let output = self.conv_fn_output(env, &decl.output)?;

        Ok(rty::FnSig::new(safety, abi, requires.into(), inputs.into(), output))
    }

    fn conv_requires(
        &mut self,
        env: &mut Env,
        requires: &fhir::Requires,
    ) -> QueryResult<rty::Expr> {
        if requires.params.is_empty() {
            self.conv_expr(env, &requires.pred)
        } else {
            env.push_layer(Layer::list(self, 0, requires.params)?);
            let pred = self.conv_expr(env, &requires.pred)?;
            let sorts = env.pop_layer().into_bound_vars(self.genv)?;
            Ok(rty::Expr::forall(rty::Binder::new(pred, sorts)))
        }
    }

    fn conv_ensures(
        &mut self,
        env: &mut Env,
        ensures: &fhir::Ensures,
    ) -> QueryResult<rty::Ensures> {
        match ensures {
            fhir::Ensures::Type(loc, ty) => {
                Ok(rty::Ensures::Type(env.lookup(loc).to_path(), self.conv_ty(env, ty)?))
            }
            fhir::Ensures::Pred(pred) => Ok(rty::Ensures::Pred(self.conv_expr(env, pred)?)),
        }
    }

    fn conv_alias_reft(
        &mut self,
        env: &mut Env,
        alias: &fhir::AliasReft,
    ) -> QueryResult<rty::AliasReft> {
        let fhir::Res::Def(DefKind::Trait, trait_id) = alias.path.res else {
            span_bug!(alias.path.span, "expected trait")
        };
        let trait_segment = alias.path.last_segment();

        let generics = self.genv.generics_of(trait_id)?;
        let self_ty =
            self.conv_ty_to_generic_arg(env, &generics.param_at(0, self.genv)?, alias.qself)?;
        let mut generic_args = vec![self_ty];
        self.conv_generic_args_into(env, trait_id, trait_segment, &mut generic_args)?;

        let alias_reft =
            rty::AliasReft { trait_id, name: alias.name, args: List::from_vec(generic_args) };
        Ok(alias_reft)
    }

    fn conv_ty(&mut self, env: &mut Env, ty: &fhir::Ty) -> QueryResult<rty::Ty> {
        match &ty.kind {
            fhir::TyKind::BaseTy(bty) => self.conv_base_ty(env, bty),
            fhir::TyKind::Indexed(bty, idx) => {
                let idx = self.conv_refine_arg(env, idx)?;
                match &bty.kind {
                    fhir::BaseTyKind::Path(fhir::QPath::Resolved(qself, path)) => {
                        debug_assert!(qself.is_none());
                        Ok(self.conv_ty_ctor(env, path)?.replace_bound_reft(&idx))
                    }
                    fhir::BaseTyKind::Path(fhir::QPath::TypeRelative(..)) => {
                        span_bug!(ty.span, "Indexed type relative paths are not yet supported");
                    }
                    fhir::BaseTyKind::Slice(ty) => {
                        let bty = rty::BaseTy::Slice(self.conv_ty(env, ty)?);
                        Ok(rty::Ty::indexed(bty, idx))
                    }
                }
            }
            fhir::TyKind::Exists(params, ty) => {
                let layer = Layer::list(self, 0, params)?;
                env.push_layer(layer);
                let ty = self.conv_ty(env, ty)?;
                let sorts = env.pop_layer().into_bound_vars(self.genv)?;
                if sorts.is_empty() {
                    Ok(ty.shift_out_escaping(1))
                } else {
                    Ok(rty::Ty::exists(rty::Binder::new(ty, sorts)))
                }
            }
            fhir::TyKind::StrgRef(lft, loc, ty) => {
                let re = self.conv_lifetime(env, *lft);
                let ty = self.conv_ty(env, ty)?;
                Ok(rty::Ty::strg_ref(re, env.lookup(loc).to_path(), ty))
            }
            fhir::TyKind::Ref(lft, fhir::MutTy { ty, mutbl }) => {
                let region = self.conv_lifetime(env, *lft);
                Ok(rty::Ty::mk_ref(region, self.conv_ty(env, ty)?, *mutbl))
            }
            fhir::TyKind::BareFn(bare_fn) => {
                let mut env = Env::empty();
                env.push_layer(Layer::list(self, bare_fn.generic_params.len() as u32, &[])?);
                let fn_sig =
                    self.conv_fn_decl(&mut env, bare_fn.safety, bare_fn.abi, bare_fn.decl)?;
                let vars = bare_fn
                    .generic_params
                    .iter()
                    .map(|param| self.param_as_bound_var(param))
                    .try_collect()?;
                let poly_fn_sig = rty::Binder::new(fn_sig, vars);
                Ok(rty::BaseTy::FnPtr(poly_fn_sig).to_ty())
            }
            fhir::TyKind::Tuple(tys) => {
                let tys: List<rty::Ty> =
                    tys.iter().map(|ty| self.conv_ty(env, ty)).try_collect()?;
                Ok(rty::Ty::tuple(tys))
            }
            fhir::TyKind::Array(ty, len) => {
                Ok(rty::Ty::array(self.conv_ty(env, ty)?, self.conv_const_arg(*len)))
            }
            fhir::TyKind::Never => Ok(rty::Ty::never()),
            fhir::TyKind::Constr(pred, ty) => {
                let pred = self.conv_expr(env, pred)?;
                Ok(rty::Ty::constr(pred, self.conv_ty(env, ty)?))
            }
            fhir::TyKind::RawPtr(ty, mutability) => {
                Ok(rty::Ty::indexed(
                    rty::BaseTy::RawPtr(self.conv_ty(env, ty)?, *mutability),
                    rty::Expr::unit(),
                ))
            }
            fhir::TyKind::OpaqueDef(item_id, lifetimes, reft_args, _in_trait) => {
                self.conv_opaque_ty(env, *item_id, lifetimes, reft_args)
            }
            fhir::TyKind::TraitObject(trait_bounds, lft, syn) => {
                if matches!(syn, rustc_ast::TraitObjectSyntax::Dyn) {
                    self.conv_trait_object(env, trait_bounds, *lft)
                } else {
                    span_bug!(ty.span, "dyn* traits not supported yet")
                }
            }
            fhir::TyKind::Infer => Ok(rty::Ty::infer(self.next_type_vid())),
        }
    }

    /// Code adapted from <https://github.com/rust-lang/rust/blob/b5723af3457b9cd3795eeb97e9af2d34964854f2/compiler/rustc_hir_analysis/src/hir_ty_lowering/mod.rs#L2099>
    fn conv_opaque_ty(
        &mut self,
        env: &mut Env,
        item_id: hir::ItemId,
        lifetimes: &[fhir::GenericArg],
        reft_args: &[fhir::RefineArg],
    ) -> QueryResult<rty::Ty> {
        let def_id = item_id.owner_id.to_def_id();
        let generics = self.genv.generics_of(def_id)?;
        let args = rty::GenericArg::for_item(self.genv, def_id, |param, _| {
            if let Some(i) = (param.index as usize).checked_sub(generics.count() - lifetimes.len())
            {
                // Resolve our own lifetime parameters.
                let rty::GenericParamDefKind::Lifetime { .. } = param.kind else {
                    span_bug!(
                        self.genv.tcx().def_span(param.def_id),
                        "only expected lifetime for opaque's own generics, got {:?}",
                        param.kind
                    );
                };
                let fhir::GenericArg::Lifetime(lft) = &lifetimes[i] else {
                    bug!(
                        "expected lifetime argument for param {param:?}, found {:?}",
                        &lifetimes[i]
                    )
                };
                rty::GenericArg::Lifetime(self.conv_lifetime(env, *lft))
            } else {
                rty::GenericArg::from_param_def(param)
            }
        })?;
        let reft_args = reft_args
            .iter()
            .map(|arg| self.conv_refine_arg(env, arg))
            .try_collect()?;
        let alias_ty = rty::AliasTy::new(def_id, args, reft_args);
        Ok(rty::Ty::alias(rty::AliasKind::Opaque, alias_ty))
    }

    fn conv_trait_object(
        &mut self,
        env: &mut Env,
        trait_bounds: &[fhir::PolyTraitRef],
        lifetime: fhir::Lifetime,
    ) -> QueryResult<rty::Ty> {
        // We convert all the trait bounds into existential predicates. Some combinations won't yield
        // valid rust types (e.g., only one regular (non-auto) trait is allowed). We don't detect those
        // errors here, but that's fine because we should catch them when we check structural
        // compatibility with the unrefined rust type. We must be careful with producing predicates
        // in the same order that rustc does.

        let mut bounds = vec![];
        let dummy_self = rty::Ty::trait_object_dummy_self();
        for trait_bound in trait_bounds.iter().rev() {
            self.conv_poly_trait_ref(env, trait_bound.span, &dummy_self, trait_bound, &mut bounds)?;
        }

        // Separate trait bounds and projections bounds
        let mut trait_bounds = vec![];
        let mut projection_bounds = vec![];
        for pred in bounds {
            let bound_pred = pred.kind();
            let vars = bound_pred.vars().clone();
            match bound_pred.skip_binder() {
                rty::ClauseKind::Trait(trait_pred) => {
                    trait_bounds.push(rty::Binder::new(trait_pred.trait_ref, vars));
                }
                rty::ClauseKind::Projection(proj) => {
                    projection_bounds.push(rty::Binder::new(proj, vars));
                }
                rty::ClauseKind::TypeOutlives(_) => {}
                rty::ClauseKind::FnTrait(..)
                | rty::ClauseKind::ConstArgHasType(..)
                | rty::ClauseKind::CoroutineOblig(..) => {
                    bug!("did not expect {pred:?} clause in object bounds");
                }
            }
        }

        // Separate between regular from auto traits
        let (mut auto_traits, regular_traits): (Vec<_>, Vec<_>) = trait_bounds
            .into_iter()
            .partition(|trait_ref| self.genv.tcx().trait_is_auto(trait_ref.def_id()));

        // De-duplicate auto traits preserving order
        {
            let mut duplicates = FxHashSet::default();
            auto_traits.retain(|trait_ref| duplicates.insert(trait_ref.def_id()));
        }

        let regular_trait_predicates = regular_traits.into_iter().map(|poly_trait_ref| {
            poly_trait_ref.map(|trait_ref| {
                // Remove dummy self
                let args = trait_ref.args.iter().skip(1).cloned().collect();
                rty::ExistentialPredicate::Trait(rty::ExistentialTraitRef {
                    def_id: trait_ref.def_id,
                    args,
                })
            })
        });

        let auto_trait_predicates = auto_traits.into_iter().map(|trait_def| {
            rty::Binder::dummy(rty::ExistentialPredicate::AutoTrait(trait_def.def_id()))
        });

        let existential_projections = projection_bounds.into_iter().map(|bound| {
            bound.map(|proj| {
                // Remove dummy self
                let args = proj.projection_ty.args.iter().skip(1).cloned().collect();
                rty::ExistentialPredicate::Projection(rty::ExistentialProjection {
                    def_id: proj.projection_ty.def_id,
                    args,
                    term: proj.term.clone(),
                })
            })
        });

        let existential_predicates = {
            let mut v = regular_trait_predicates
                .chain(existential_projections)
                .chain(auto_trait_predicates)
                .collect_vec();
            v.sort_by(|a, b| {
                a.as_ref()
                    .skip_binder()
                    .stable_cmp(self.genv.tcx(), b.as_ref().skip_binder())
            });
            List::from_vec(v)
        };

        let region = self.conv_lifetime(env, lifetime);
        Ok(rty::Ty::dynamic(existential_predicates, region))
    }

    fn conv_base_ty(&mut self, env: &mut Env, bty: &fhir::BaseTy) -> QueryResult<rty::Ty> {
        match &bty.kind {
            fhir::BaseTyKind::Path(fhir::QPath::Resolved(qself, path)) => {
                match path.res {
                    fhir::Res::Def(DefKind::AssocTy, assoc_id) => {
                        let trait_id = self.genv.tcx().trait_of_item(assoc_id).unwrap();
                        let [.., trait_segment, assoc_segment] = path.segments else {
                            span_bug!(bty.span, "expected at least two segments");
                        };

                        let trait_generics = self.genv.generics_of(trait_id)?;
                        let qself = qself.as_deref().unwrap();
                        let qself =
                            self.conv_ty_to_generic_arg(env, &trait_generics.own_params[0], qself)?;
                        let mut args = vec![qself];
                        self.conv_generic_args_into(env, trait_id, trait_segment, &mut args)?;
                        self.conv_generic_args_into(env, assoc_id, assoc_segment, &mut args)?;
                        let args = List::from_vec(args);

                        let refine_args = List::empty();
                        let alias_ty = rty::AliasTy { args, refine_args, def_id: assoc_id };
                        return Ok(rty::Ty::alias(rty::AliasKind::Projection, alias_ty));
                    }
                    fhir::Res::SelfTyParam { trait_ } => {
                        let param = self.genv.generics_of(trait_)?.param_at(0, self.genv)?;
                        if let rty::GenericParamDefKind::Type { .. } = param.kind {
                            return Ok(rty::Ty::param(rty::SELF_PARAM_TY));
                        }
                    }
                    fhir::Res::Def(DefKind::TyParam, def_id) => {
                        let owner_id = self.genv.tcx().parent(def_id);
                        let param_ty = def_id_to_param_ty(self.genv, def_id);
                        let param = self
                            .genv
                            .generics_of(owner_id)?
                            .param_at(param_ty.index as usize, self.genv)?;
                        if let rty::GenericParamDefKind::Type { .. } = param.kind {
                            return Ok(rty::Ty::param(param_ty));
                        }
                    }
                    _ => {}
                }
                Ok(self.conv_ty_ctor(env, path)?.to_ty())
            }
            fhir::BaseTyKind::Path(fhir::QPath::TypeRelative(qself, segment)) => {
                self.conv_assoc_path(env, qself, segment)
            }
            fhir::BaseTyKind::Slice(ty) => {
                let bty = rty::BaseTy::Slice(self.conv_ty(env, ty)?).shift_in_escaping(1);
                let sort = bty.sort();
                Ok(rty::Ty::exists(rty::Binder::with_sort(
                    rty::Ty::indexed(bty, rty::Expr::nu()),
                    sort,
                )))
            }
        }
    }

    fn conv_assoc_path(
        &mut self,
        env: &mut Env,
        qself: &fhir::Ty,
        assoc_segment: &fhir::PathSegment,
    ) -> QueryResult<rty::Ty> {
        let tcx = self.genv.tcx();
        let assoc_ident = assoc_segment.ident;
        let qself_res = if let Some(path) = qself.as_path() { path.res } else { fhir::Res::Err };

        let bound = match qself_res {
            fhir::Res::SelfTyAlias { alias_to: impl_def_id, is_trait_impl: true } => {
                let Some(trait_ref) = tcx.impl_trait_ref(impl_def_id) else {
                    // A cycle error ocurred most likely (comment copied from rustc)
                    span_bug!(qself.span, "expected cycle error");
                };

                self.probe_single_bound_for_assoc_item(
                    || {
                        traits::supertraits(
                            tcx,
                            ty::Binder::dummy(trait_ref.instantiate_identity()),
                        )
                    },
                    assoc_ident,
                )?
            }
            fhir::Res::Def(DefKind::TyParam, param_did)
            | fhir::Res::SelfTyParam { trait_: param_did } => {
                let predicates = self
                    .probe_type_param_bounds(param_did.expect_local(), assoc_ident)
                    .predicates;
                self.probe_single_bound_for_assoc_item(
                    || {
                        traits::transitive_bounds_that_define_assoc_item(
                            tcx,
                            predicates.iter().filter_map(|(p, _)| {
                                Some(p.as_trait_clause()?.map_bound(|t| t.trait_ref))
                            }),
                            assoc_ident,
                        )
                    },
                    assoc_ident,
                )?
            }
            _ => {
                Err(self
                    .genv
                    .sess()
                    .emit_err(errors::AssocTypeNotFound::new(assoc_ident)))?
            }
        };

        let Some(trait_ref) = bound.no_bound_vars() else {
            // This is a programmer error and we should gracefully report it. It's triggered
            // by code like this
            // ```
            // trait Super<'a> { type Assoc; }
            // trait Child: for<'a> Super<'a> {}
            // fn foo<T: Child>(x: T::Assoc) {}
            // ```
            Err(self.genv.sess().emit_err(
                query_bug!("associated path with uninferred generic parameters")
                    .at(assoc_ident.span),
            ))?
        };

        let trait_ref = {
            let generics = self.generics_of_owner()?;
            let trait_ref = self.genv.lower_trait_ref(trait_ref)?;
            Refiner::default(self.genv, &generics).refine_trait_ref(&trait_ref)?
        };

        let assoc_item = self
            .trait_defines_associated_item_named(trait_ref.def_id, AssocKind::Type, assoc_ident)
            .unwrap();

        let assoc_id = assoc_item.def_id;

        let mut args = trait_ref.args.to_vec();
        self.conv_generic_args_into(env, assoc_id, assoc_segment, &mut args)?;

        let args = List::from_vec(args);
        let refine_args = List::empty();
        let alias_ty = rty::AliasTy { args, refine_args, def_id: assoc_id };
        Ok(rty::Ty::alias(rty::AliasKind::Projection, alias_ty))
    }

    /// Return the generics of the containing owner item
    fn generics_of_owner(&self) -> QueryResult<rty::Generics> {
        match self.owner() {
            FluxOwnerId::Rust(owner_id) => self.genv.generics_of(owner_id),
            FluxOwnerId::Flux(_) => Ok(rty::Generics::default()),
        }
    }

    fn probe_type_param_bounds(
        &self,
        param_did: LocalDefId,
        assoc_ident: Ident,
    ) -> ty::GenericPredicates<'tcx> {
        match self.owner() {
            FluxOwnerId::Rust(owner_id) => {
                self.genv
                    .tcx()
                    .type_param_predicates((owner_id.def_id, param_did, assoc_ident))
            }
            FluxOwnerId::Flux(_) => ty::GenericPredicates::default(),
        }
    }

    fn probe_single_bound_for_assoc_item<I>(
        &self,
        all_candidates: impl Fn() -> I,
        assoc_ident: rustc_span::symbol::Ident,
    ) -> Result<ty::PolyTraitRef<'tcx>, ErrorGuaranteed>
    where
        I: Iterator<Item = ty::PolyTraitRef<'tcx>>,
    {
        let mut matching_candidates = all_candidates().filter(|r| {
            self.trait_defines_associated_item_named(r.def_id(), AssocKind::Type, assoc_ident)
                .is_some()
        });

        let Some(bound) = matching_candidates.next() else {
            return Err(self
                .genv
                .sess()
                .emit_err(errors::AssocTypeNotFound::new(assoc_ident)));
        };

        if matching_candidates.next().is_some() {
            return Err(self
                .genv
                .sess()
                .emit_err(errors::AmbiguousAssocType::new(assoc_ident)));
        }

        Ok(bound)
    }

    fn conv_lifetime(&mut self, env: &Env, lft: fhir::Lifetime) -> rty::Region {
        let res = match lft {
            fhir::Lifetime::Hole(_) => return rty::Region::ReVar(self.next_region_vid()),
            fhir::Lifetime::Resolved(res) => res,
        };
        let tcx = self.genv.tcx();
        let lifetime_name = |def_id| tcx.hir().name(tcx.local_def_id_to_hir_id(def_id));
        match res {
            ResolvedArg::StaticLifetime => rty::ReStatic,
            ResolvedArg::EarlyBound(def_id) => {
                let index = self.genv.def_id_to_param_index(def_id);
                let name = lifetime_name(def_id.expect_local());
                rty::ReEarlyParam(rty::EarlyParamRegion { index, name })
            }
            ResolvedArg::LateBound(_, index, def_id) => {
                let depth = env.depth().checked_sub(1).unwrap();
                let name = lifetime_name(def_id.expect_local());
                let kind = rty::BoundRegionKind::BrNamed(def_id, name);
                let var = BoundVar::from_u32(index);
                let bound_region = rty::BoundRegion { var, kind };
                rty::ReBound(rty::DebruijnIndex::from_usize(depth), bound_region)
            }
            ResolvedArg::Free(scope, id) => {
                let name = lifetime_name(id.expect_local());
                let bound_region = rty::BoundRegionKind::BrNamed(id, name);
                rty::ReLateParam(rty::LateParamRegion { scope, bound_region })
            }
            ResolvedArg::Error(_) => bug!("lifetime resolved to an error"),
        }
    }

    fn conv_const_arg(&mut self, cst: fhir::ConstArg) -> rty::Const {
        match cst.kind {
            fhir::ConstArgKind::Lit(lit) => rty::Const::from_usize(self.genv.tcx(), lit),
            fhir::ConstArgKind::Param(def_id) => {
                rty::Const {
                    kind: rty::ConstKind::Param(
                        self.genv.def_id_to_param_const(def_id.expect_local()),
                    ),
                }
            }
            fhir::ConstArgKind::Infer => {
                rty::Const {
                    kind: rty::ConstKind::Infer(ty::InferConst::Var(self.next_const_vid())),
                }
            }
        }
    }

    fn conv_ty_ctor(&mut self, env: &mut Env, path: &fhir::Path) -> QueryResult<rty::TyCtor> {
        let bty = match &path.res {
            fhir::Res::PrimTy(PrimTy::Bool) => rty::BaseTy::Bool,
            fhir::Res::PrimTy(PrimTy::Str) => rty::BaseTy::Str,
            fhir::Res::PrimTy(PrimTy::Char) => rty::BaseTy::Char,
            fhir::Res::PrimTy(PrimTy::Int(int_ty)) => {
                rty::BaseTy::Int(rustc_middle::ty::int_ty(*int_ty))
            }
            fhir::Res::PrimTy(PrimTy::Uint(uint_ty)) => {
                rty::BaseTy::Uint(rustc_middle::ty::uint_ty(*uint_ty))
            }
            fhir::Res::PrimTy(PrimTy::Float(float_ty)) => {
                rty::BaseTy::Float(rustc_middle::ty::float_ty(*float_ty))
            }
            fhir::Res::Def(DefKind::Struct | DefKind::Enum, did) => {
                let adt_def = self.genv.adt_def(*did)?;
                let args = self.conv_generic_args(env, *did, path.last_segment())?;
                rty::BaseTy::adt(adt_def, args)
            }
            fhir::Res::Def(DefKind::TyParam, def_id) => {
                rty::BaseTy::Param(def_id_to_param_ty(self.genv, *def_id))
            }
            fhir::Res::SelfTyParam { .. } => rty::BaseTy::Param(rty::SELF_PARAM_TY),
            fhir::Res::SelfTyAlias { alias_to, .. } => {
                return Ok(self.genv.type_of(*alias_to)?.instantiate_identity());
            }
            fhir::Res::Def(DefKind::TyAlias { .. }, def_id) => {
                let generics = self.conv_generic_args(env, *def_id, path.last_segment())?;
                let refine = path
                    .refine
                    .iter()
                    .map(|arg| self.conv_refine_arg(env, arg))
                    .try_collect_vec()?;
                let tcx = self.genv.tcx();
                return Ok(self
                    .genv
                    .type_of(*def_id)?
                    .instantiate(tcx, &generics, &refine));
            }
            fhir::Res::Def(..) | fhir::Res::Err => {
                span_bug!(path.span, "unexpected resolution in conv_ty_ctor: {:?}", path.res)
            }
        };
        let sort = bty.sort();
        let bty = bty.shift_in_escaping(1);
        Ok(rty::Binder::with_sort(rty::Ty::indexed(bty, rty::Expr::nu()), sort))
    }

    fn param_as_bound_var(
        &mut self,
        param: &fhir::GenericParam,
    ) -> QueryResult<rty::BoundVariableKind> {
        let def_id = param.def_id.to_def_id();
        let name = self.genv.tcx().item_name(def_id);
        match param.kind {
            fhir::GenericParamKind::Lifetime => {
                Ok(rty::BoundVariableKind::Region(BrNamed(def_id, name)))
            }
            fhir::GenericParamKind::Const { .. }
            | fhir::GenericParamKind::Type { .. }
            | fhir::GenericParamKind::Base => {
                Err(query_bug!(param.def_id, "unsupported param kind `{:?}`", param.kind))
            }
        }
    }

    fn conv_generic_args(
        &mut self,
        env: &mut Env,
        def_id: DefId,
        segment: &fhir::PathSegment,
    ) -> QueryResult<Vec<rty::GenericArg>> {
        let mut into = vec![];
        self.conv_generic_args_into(env, def_id, segment, &mut into)?;
        Ok(into)
    }

    fn conv_generic_args_into(
        &mut self,
        env: &mut Env,
        def_id: DefId,
        segment: &fhir::PathSegment,
        into: &mut Vec<rty::GenericArg>,
    ) -> QueryResult {
        let generics = self.genv.generics_of(def_id)?;

        self.check_generic_arg_count(&generics, def_id, segment)?;

        let len = into.len();
        for (idx, arg) in segment.args.iter().enumerate() {
            let param = generics.param_at(idx + len, self.genv)?;
            match arg {
                fhir::GenericArg::Lifetime(lft) => {
                    into.push(rty::GenericArg::Lifetime(self.conv_lifetime(env, *lft)));
                }
                fhir::GenericArg::Type(ty) => {
                    into.push(self.conv_ty_to_generic_arg(env, &param, ty)?);
                }
                fhir::GenericArg::Const(cst) => {
                    into.push(rty::GenericArg::Const(self.conv_const_arg(*cst)));
                }
            }
        }
        self.fill_generic_args_defaults(def_id, into)
    }

    fn check_generic_arg_count(
        &mut self,
        generics: &rty::Generics,
        def_id: DefId,
        segment: &fhir::PathSegment,
    ) -> QueryResult {
        let found = segment.args.len();
        let mut param_count = generics.own_params.len();

        // The self parameter is not provided explicitly in the path so we skip it
        if let DefKind::Trait = self.genv.def_kind(def_id) {
            param_count -= 1;
        }

        let min = param_count - generics.own_default_count();
        let max = param_count;
        if min == max && found != min {
            Err(self.emit(errors::GenericArgCountMismatch::new(self.genv, def_id, segment, min)))?;
        }
        if found < min {
            Err(self.emit(errors::TooFewGenericArgs::new(self.genv, def_id, segment, min)))?;
        }
        if found > max {
            Err(self.emit(errors::TooManyGenericArgs::new(self.genv, def_id, segment, min)))?;
        }
        Ok(())
    }

    fn fill_generic_args_defaults(
        &self,
        def_id: DefId,
        into: &mut Vec<rty::GenericArg>,
    ) -> QueryResult {
        let generics = self.genv.generics_of(def_id)?;
        for param in generics.own_params.iter().skip(into.len()) {
            if let rty::GenericParamDefKind::Type { has_default } = param.kind {
                debug_assert!(has_default);
                let tcx = self.genv.tcx();
                let ty = self
                    .genv
                    .type_of(param.def_id)?
                    .instantiate(tcx, into, &[])
                    .to_ty();
                into.push(rty::GenericArg::Ty(ty));
            } else {
                bug!("unexpected generic param: {param:?}");
            }
        }
        Ok(())
    }

    fn conv_ty_to_generic_arg(
        &mut self,
        env: &mut Env,
        param: &rty::GenericParamDef,
        ty: &fhir::Ty,
    ) -> QueryResult<rty::GenericArg> {
        let rty_ty = self.conv_ty(env, ty)?;
        match &param.kind {
            rty::GenericParamDefKind::Type { .. } => Ok(rty::GenericArg::Ty(rty_ty)),
            rty::GenericParamDefKind::Base => self.ty_to_base_generic(ty.span, &rty_ty),
            _ => bug!("unexpected param `{param:?}`"),
        }
    }

    fn ty_to_generic_arg(
        &self,
        kind: rty::GenericParamDefKind,
        span: Span,
        ty: &rty::Ty,
    ) -> QueryResult<rty::GenericArg> {
        match kind {
            rty::GenericParamDefKind::Type { .. } => Ok(rty::GenericArg::Ty(ty.clone())),
            rty::GenericParamDefKind::Base => self.ty_to_base_generic(span, ty),
            _ => span_bug!(span, "unexpected param kind `{kind:?}`"),
        }
    }

    /// Convert an [`rty::Ty`] into a [`rty::GenericArg::Base`] if possible or raise an error
    /// if the type cannot be converted into a [`rty::SubsetTy`].
    fn ty_to_base_generic(&self, span: Span, ty: &rty::Ty) -> QueryResult<rty::GenericArg> {
        let ctor = ty
            .shallow_canonicalize()
            .to_subset_ty_ctor()
            .ok_or_else(|| {
                self.genv
                    .sess()
                    .emit_err(errors::InvalidBaseInstance::new(span))
            })?;
        Ok(rty::GenericArg::Base(ctor))
    }

    fn resolve_param_sort(&self, param: &fhir::RefineParam) -> QueryResult<rty::Sort> {
        resolve_param_sort(self.genv, param, Some(self.wfckresults))
    }

    fn next_type_vid(&mut self) -> rty::TyVid {
        self.next_type_index = self.next_type_index.checked_add(1).unwrap();
        rty::TyVid::from_u32(self.next_type_index - 1)
    }

    fn next_region_vid(&mut self) -> rty::RegionVid {
        self.next_region_index = self.next_region_index.checked_add(1).unwrap();
        rty::RegionVid::from_u32(self.next_region_index - 1)
    }

    fn next_const_vid(&mut self) -> rty::ConstVid {
        self.next_const_index = self.next_const_index.checked_add(1).unwrap();
        rty::ConstVid::from_u32(self.next_const_index - 1)
    }

    #[track_caller]
    fn emit<'b>(&'b self, err: impl Diagnostic<'b>) -> ErrorGuaranteed {
        self.genv.sess().emit_err(err)
    }
}

impl Env {
    fn new(
        genv: GlobalEnv,
        early_bound: &[fhir::RefineParam],
        wfckresults: &WfckResults,
    ) -> QueryResult<Self> {
        let early_bound = early_bound
            .iter()
            .map(|param| -> QueryResult<_> {
                let sort = resolve_param_sort(genv, param, Some(wfckresults))?;
                Ok((param.id, (param.name, sort)))
            })
            .try_collect()?;
        Ok(Self { layers: vec![], early_bound })
    }

    fn empty() -> Self {
        Self { layers: vec![], early_bound: Default::default() }
    }

    fn depth(&self) -> usize {
        self.layers.len()
    }

    fn push_layer(&mut self, layer: Layer) {
        self.layers.push(layer);
    }

    fn pop_layer(&mut self) -> Layer {
        self.layers.pop().expect("bottom of layer stack")
    }

    fn top_layer(&self) -> &Layer {
        self.layers.last().expect("bottom of layer stack")
    }

    fn lookup(&self, var: &fhir::PathExpr) -> LookupResult {
        let (_, id) = var.res.expect_param();
        for (i, layer) in self.layers.iter().rev().enumerate() {
            if let Some((idx, entry)) = layer.get(id) {
                let debruijn = DebruijnIndex::from_usize(i);
                let kind = LookupResultKind::LateBound {
                    debruijn,
                    entry,
                    index: idx as u32,
                    kind: layer.kind,
                };
                return LookupResult { var_span: var.span, kind };
            }
        }
        if let Some((idx, _, (name, sort))) = self.early_bound.get_full(&id) {
            LookupResult {
                var_span: var.span,
                kind: LookupResultKind::EarlyParam {
                    index: idx as u32,
                    name: *name,
                    sort: sort.clone(),
                },
            }
        } else {
            span_bug!(var.span, "no entry found for key: `{:?}`", id);
        }
    }

    fn to_early_bound_vars(&self) -> List<rty::Expr> {
        self.early_bound
            .iter()
            .enumerate()
            .map(|(idx, (_, (name, _)))| rty::Expr::early_param(idx as u32, *name))
            .collect()
    }
}

impl ConvCtxt<'_, '_, '_> {
    fn owner(&self) -> FluxOwnerId {
        self.wfckresults.owner
    }

    fn conv_refine_arg(&mut self, env: &mut Env, arg: &fhir::RefineArg) -> QueryResult<rty::Expr> {
        match &arg.kind {
            fhir::RefineArgKind::Expr(expr) => self.conv_expr(env, expr),
            fhir::RefineArgKind::Abs(params, body) => {
                let layer = Layer::list(self, 0, params)?;

                env.push_layer(layer);
                let pred = self.conv_expr(env, body)?;
                let inputs = env.pop_layer().into_bound_vars(self.genv)?;
                let output = self
                    .wfckresults
                    .node_sorts()
                    .get(arg.fhir_id)
                    .unwrap_or_else(|| bug!("lambda without elaborated sort"))
                    .clone();
                let lam = rty::Lambda::with_vars(pred, inputs, output);
                Ok(self.add_coercions(rty::Expr::abs(lam), arg.fhir_id))
            }
            fhir::RefineArgKind::Record(flds) => {
                let def_id = self.wfckresults.record_ctors().get(arg.fhir_id).unwrap();
                let flds = flds
                    .iter()
                    .map(|arg| self.conv_refine_arg(env, arg))
                    .try_collect()?;
                Ok(rty::Expr::adt(*def_id, flds))
            }
        }
    }

    fn conv_expr(&mut self, env: &mut Env, expr: &fhir::Expr) -> QueryResult<rty::Expr> {
        let fhir_id = expr.fhir_id;
        let espan = ESpan::new(expr.span);
        let expr = match &expr.kind {
            fhir::ExprKind::Var(var, _) => {
                match var.res {
                    ExprRes::Param(..) => env.lookup(var).to_expr(),
                    ExprRes::Const(def_id) => rty::Expr::const_def_id(def_id).at(espan),
                    ExprRes::ConstGeneric(def_id) => {
                        rty::Expr::const_generic(
                            self.genv.def_id_to_param_const(def_id.expect_local()),
                        )
                        .at(espan)
                    }
                    ExprRes::NumConst(num) => {
                        rty::Expr::constant(rty::Constant::from(num)).at(espan)
                    }
                    ExprRes::GlobalFunc(..) => {
                        span_bug!(var.span, "unexpected func in var position")
                    }
                }
            }
            fhir::ExprKind::Literal(lit) => rty::Expr::constant(conv_lit(*lit)).at(espan),
            fhir::ExprKind::BinaryOp(op, e1, e2) => {
                rty::Expr::binary_op(
                    self.conv_bin_op(*op, expr.fhir_id),
                    self.conv_expr(env, e1)?,
                    self.conv_expr(env, e2)?,
                )
                .at(espan)
            }
            fhir::ExprKind::UnaryOp(op, e) => {
                rty::Expr::unary_op(conv_un_op(*op), self.conv_expr(env, e)?).at(espan)
            }
            fhir::ExprKind::App(func, args) => {
                rty::Expr::app(self.conv_func(env, func), self.conv_exprs(env, args)?).at(espan)
            }
            fhir::ExprKind::Alias(alias, args) => {
                let args = args
                    .iter()
                    .map(|arg| self.conv_expr(env, arg))
                    .try_collect()?;
                let alias = self.conv_alias_reft(env, alias)?;
                rty::Expr::alias(alias, args).at(espan)
            }
            fhir::ExprKind::IfThenElse(p, e1, e2) => {
                rty::Expr::ite(
                    self.conv_expr(env, p)?,
                    self.conv_expr(env, e1)?,
                    self.conv_expr(env, e2)?,
                )
                .at(espan)
            }
            fhir::ExprKind::Dot(var, fld) => env.lookup(var).get_field(*fld, espan),
        };
        Ok(self.add_coercions(expr, fhir_id))
    }

    fn conv_bin_op(&self, op: fhir::BinOp, fhir_id: FhirId) -> rty::BinOp {
        match op {
            fhir::BinOp::Iff => rty::BinOp::Iff,
            fhir::BinOp::Imp => rty::BinOp::Imp,
            fhir::BinOp::Or => rty::BinOp::Or,
            fhir::BinOp::And => rty::BinOp::And,
            fhir::BinOp::Eq => rty::BinOp::Eq,
            fhir::BinOp::Ne => rty::BinOp::Ne,
            fhir::BinOp::Gt => rty::BinOp::Gt(self.bin_rel_sort(fhir_id)),
            fhir::BinOp::Ge => rty::BinOp::Ge(self.bin_rel_sort(fhir_id)),
            fhir::BinOp::Lt => rty::BinOp::Lt(self.bin_rel_sort(fhir_id)),
            fhir::BinOp::Le => rty::BinOp::Le(self.bin_rel_sort(fhir_id)),
            fhir::BinOp::Add => rty::BinOp::Add,
            fhir::BinOp::Sub => rty::BinOp::Sub,
            fhir::BinOp::Mod => rty::BinOp::Mod,
            fhir::BinOp::Mul => rty::BinOp::Mul,
            fhir::BinOp::Div => rty::BinOp::Div,
        }
    }

    fn bin_rel_sort(&self, fhir_id: FhirId) -> rty::Sort {
        self.wfckresults
            .bin_rel_sorts()
            .get(fhir_id)
            .unwrap()
            .clone()
    }

    fn conv_func(&self, env: &Env, func: &fhir::PathExpr) -> rty::Expr {
        let expr = match func.res {
            ExprRes::Param(..) => env.lookup(func).to_expr(),
            ExprRes::GlobalFunc(kind, sym) => rty::Expr::global_func(sym, kind),
            _ => span_bug!(func.span, "unexpected path in function position"),
        };
        self.add_coercions(expr, func.fhir_id)
    }

    fn conv_exprs(&mut self, env: &mut Env, exprs: &[fhir::Expr]) -> QueryResult<List<rty::Expr>> {
        exprs.iter().map(|e| self.conv_expr(env, e)).collect()
    }

    fn conv_invariants(
        &mut self,
        env: &mut Env,
        invariants: &[fhir::Expr],
    ) -> QueryResult<Vec<rty::Invariant>> {
        invariants
            .iter()
            .map(|invariant| self.conv_invariant(env, invariant))
            .collect()
    }

    fn conv_invariant(
        &mut self,
        env: &mut Env,
        invariant: &fhir::Expr,
    ) -> QueryResult<rty::Invariant> {
        Ok(rty::Invariant::new(rty::Binder::new(
            self.conv_expr(env, invariant)?,
            env.top_layer().to_bound_vars(self.genv)?,
        )))
    }

    fn add_coercions(&self, mut expr: rty::Expr, fhir_id: FhirId) -> rty::Expr {
        let span = expr.span();
        if let Some(coercions) = self.wfckresults.coercions().get(fhir_id) {
            for coercion in coercions {
                expr = match *coercion {
                    rty::Coercion::Inject(def_id) => {
                        rty::Expr::aggregate(rty::AggregateKind::Adt(def_id), List::singleton(expr))
                            .at_opt(span)
                    }
                    rty::Coercion::Project(def_id) => {
                        rty::Expr::field_proj(expr, rty::FieldProj::Adt { def_id, field: 0 })
                            .at_opt(span)
                    }
                };
            }
        }
        expr
    }
}

impl Layer {
    fn new(cx: &ConvCtxt, params: &[fhir::RefineParam], kind: LayerKind) -> QueryResult<Self> {
        let map = params
            .iter()
            .map(|param| -> QueryResult<_> {
                let sort = cx.resolve_param_sort(param)?;
                let infer_mode = rty::InferMode::from_param_kind(param.kind);
                let entry = ParamEntry::new(sort, infer_mode, param.name);
                Ok((param.id, entry))
            })
            .try_collect()?;
        Ok(Self { map, kind })
    }

    fn list(cx: &ConvCtxt, bound_regions: u32, params: &[fhir::RefineParam]) -> QueryResult<Self> {
        Self::new(cx, params, LayerKind::List { bound_regions })
    }

    fn coalesce(cx: &ConvCtxt, def_id: DefId, params: &[fhir::RefineParam]) -> QueryResult<Self> {
        Self::new(cx, params, LayerKind::Coalesce(def_id))
    }

    fn get(&self, name: impl Borrow<fhir::ParamId>) -> Option<(usize, &ParamEntry)> {
        let (idx, _, entry) = self.map.get_full(name.borrow())?;
        Some((idx, entry))
    }

    fn into_bound_vars(self, genv: GlobalEnv) -> QueryResult<List<rty::BoundVariableKind>> {
        match self.kind {
            LayerKind::List { .. } => {
                Ok(self
                    .into_iter()
                    .map(|entry| {
                        let kind = rty::BoundReftKind::Named(entry.name);
                        rty::BoundVariableKind::Refine(entry.sort, entry.mode, kind)
                    })
                    .collect())
            }
            LayerKind::Coalesce(def_id) => {
                let sort_def = genv.adt_sort_def_of(def_id)?;
                let args = sort_def.identity_args();
                let ctor = rty::SortCtor::Adt(sort_def);
                Ok(List::singleton(rty::BoundVariableKind::Refine(
                    rty::Sort::App(ctor, args),
                    rty::InferMode::EVar,
                    rty::BoundReftKind::Annon,
                )))
            }
        }
    }

    fn to_bound_vars(&self, genv: GlobalEnv) -> QueryResult<List<rty::BoundVariableKind>> {
        self.clone().into_bound_vars(genv)
    }

    fn into_iter(self) -> impl Iterator<Item = ParamEntry> {
        self.map.into_values()
    }
}

impl ParamEntry {
    fn new(sort: rty::Sort, mode: fhir::InferMode, name: Symbol) -> Self {
        ParamEntry { name, sort, mode }
    }
}

impl LookupResult<'_> {
    fn to_expr(&self) -> rty::Expr {
        let espan = ESpan::new(self.var_span);
        match &self.kind {
            LookupResultKind::LateBound {
                debruijn,
                entry: ParamEntry { name, .. },
                kind,
                index,
            } => {
                match *kind {
                    LayerKind::List { bound_regions } => {
                        rty::Expr::bvar(
                            *debruijn,
                            BoundVar::from_u32(bound_regions + *index),
                            rty::BoundReftKind::Named(*name),
                        )
                        .at(espan)
                    }
                    LayerKind::Coalesce(def_id) => {
                        let var =
                            rty::Expr::bvar(*debruijn, BoundVar::ZERO, rty::BoundReftKind::Annon)
                                .at(espan);
                        rty::Expr::field_proj(var, rty::FieldProj::Adt { def_id, field: *index })
                            .at(espan)
                    }
                }
            }
            &LookupResultKind::EarlyParam { index, name, .. } => {
                rty::Expr::early_param(index, name).at(espan)
            }
        }
    }

    fn is_adt(&self) -> Option<&AdtSortDef> {
        match &self.kind {
            LookupResultKind::LateBound {
                entry: ParamEntry { sort: rty::Sort::App(rty::SortCtor::Adt(sort_def), _), .. },
                ..
            } => Some(sort_def),
            LookupResultKind::EarlyParam {
                sort: rty::Sort::App(rty::SortCtor::Adt(sort_def), _),
                ..
            } => Some(sort_def),
            _ => None,
        }
    }

    fn to_path(&self) -> rty::Path {
        self.to_expr().to_path().unwrap_or_else(|| {
            span_bug!(self.var_span, "expected path, found `{:?}`", self.to_expr())
        })
    }

    fn get_field(&self, fld: Ident, espan: ESpan) -> rty::Expr {
        if let Some(sort_def) = self.is_adt() {
            let def_id = sort_def.did();
            let i = sort_def
                .field_index(fld.name)
                .unwrap_or_else(|| span_bug!(fld.span, "field `{fld:?}` not found in {def_id:?}"));
            rty::Expr::field_proj(self.to_expr(), rty::FieldProj::Adt { def_id, field: i as u32 })
                .at(espan)
        } else {
            span_bug!(fld.span, "expected adt sort")
        }
    }
}

pub fn conv_func_decl(genv: GlobalEnv, func: &fhir::SpecFunc) -> QueryResult<rty::SpecFuncDecl> {
    let inputs_and_output = func
        .args
        .iter()
        .map(|p| &p.sort)
        .chain(iter::once(&func.sort))
        .map(|sort| conv_sort(genv, sort, &mut bug_on_infer_sort))
        .try_collect()?;
    let params = iter::repeat(rty::SortParamKind::Sort)
        .take(func.params)
        .collect();
    let sort = rty::PolyFuncSort::new(params, rty::FuncSort { inputs_and_output });
    let kind = if func.body.is_some() { fhir::SpecFuncKind::Def } else { fhir::SpecFuncKind::Uif };
    Ok(rty::SpecFuncDecl { name: func.name, sort, kind })
}

fn conv_sorts(
    genv: GlobalEnv,
    sorts: &[fhir::Sort],
    next_infer_sort: &mut impl FnMut() -> rty::Sort,
) -> QueryResult<Vec<rty::Sort>> {
    sorts
        .iter()
        .map(|sort| conv_sort(genv, sort, next_infer_sort))
        .try_collect()
}

pub(crate) fn resolve_param_sort(
    genv: GlobalEnv,
    param: &fhir::RefineParam,
    wfckresults: Option<&WfckResults>,
) -> QueryResult<rty::Sort> {
    if let fhir::Sort::Infer = &param.sort {
        Ok(wfckresults
            .expect("`Sort::Infer` without wfckresults")
            .node_sorts()
            .get(param.fhir_id)
            .unwrap_or_else(|| bug!("unresolved sort for param: `{param:?}`"))
            .clone())
    } else {
        conv_sort(genv, &param.sort, &mut bug_on_infer_sort)
    }
}

pub(crate) fn conv_sort(
    genv: GlobalEnv,
    sort: &fhir::Sort,
    next_infer_sort: &mut impl FnMut() -> rty::Sort,
) -> QueryResult<rty::Sort> {
    let sort = match sort {
        fhir::Sort::Path(path) => conv_sort_path(genv, path, next_infer_sort)?,
        fhir::Sort::BitVec(size) => rty::Sort::BitVec(rty::BvSize::Fixed(*size)),
        fhir::Sort::Loc => rty::Sort::Loc,
        fhir::Sort::Func(fsort) => {
            rty::Sort::Func(conv_poly_func_sort(genv, fsort, next_infer_sort)?)
        }
        fhir::Sort::Infer => next_infer_sort(),
    };
    Ok(sort)
}

fn conv_sort_path(
    genv: GlobalEnv,
    path: &fhir::SortPath,
    next_infer_sort: &mut impl FnMut() -> rty::Sort,
) -> QueryResult<rty::Sort> {
    let ctor = match path.res {
        fhir::SortRes::PrimSort(fhir::PrimSort::Int) => return Ok(rty::Sort::Int),
        fhir::SortRes::PrimSort(fhir::PrimSort::Bool) => return Ok(rty::Sort::Bool),
        fhir::SortRes::PrimSort(fhir::PrimSort::Real) => return Ok(rty::Sort::Real),
        fhir::SortRes::SortParam(n) => return Ok(rty::Sort::Var(rty::ParamSort::from(n))),
        fhir::SortRes::TyParam(def_id) => {
            return Ok(rty::Sort::Param(def_id_to_param_ty(genv, def_id)))
        }
        fhir::SortRes::SelfParam { .. } => return Ok(rty::Sort::Param(rty::SELF_PARAM_TY)),
        fhir::SortRes::SelfAlias { alias_to } => {
            return Ok(genv
                .sort_of_self_ty_alias(alias_to)?
                .unwrap_or(rty::Sort::Err))
        }
        fhir::SortRes::PrimSort(fhir::PrimSort::Set) => rty::SortCtor::Set,
        fhir::SortRes::PrimSort(fhir::PrimSort::Map) => rty::SortCtor::Map,
        fhir::SortRes::User { name } => rty::SortCtor::User { name },
        fhir::SortRes::Adt(def_id) => {
            let sort_def = genv.adt_sort_def_of(def_id)?;
            rty::SortCtor::Adt(sort_def)
        }
    };
    let args = path
        .args
        .iter()
        .map(|t| conv_sort(genv, t, next_infer_sort))
        .try_collect()?;
    Ok(rty::Sort::app(ctor, args))
}

fn conv_poly_func_sort(
    genv: GlobalEnv,
    sort: &fhir::PolyFuncSort,
    next_infer_sort: &mut impl FnMut() -> rty::Sort,
) -> QueryResult<rty::PolyFuncSort> {
    let params = iter::repeat(rty::SortParamKind::Sort)
        .take(sort.params)
        .collect();
    Ok(rty::PolyFuncSort::new(params, conv_func_sort(genv, &sort.fsort, next_infer_sort)?))
}

pub(crate) fn conv_func_sort(
    genv: GlobalEnv,
    fsort: &fhir::FuncSort,
    next_infer_sort: &mut impl FnMut() -> rty::Sort,
) -> QueryResult<rty::FuncSort> {
    Ok(rty::FuncSort::new(
        conv_sorts(genv, fsort.inputs(), next_infer_sort)?,
        conv_sort(genv, fsort.output(), next_infer_sort)?,
    ))
}

fn conv_lit(lit: fhir::Lit) -> rty::Constant {
    match lit {
        fhir::Lit::Int(n) => rty::Constant::from(n),
        fhir::Lit::Real(r) => rty::Constant::Real(rty::Real(r)),
        fhir::Lit::Bool(b) => rty::Constant::from(b),
        fhir::Lit::Str(s) => rty::Constant::from(s),
    }
}

pub(crate) fn bug_on_infer_sort() -> rty::Sort {
    bug!("unexpected infer sort")
}

fn conv_un_op(op: fhir::UnOp) -> rty::UnOp {
    match op {
        fhir::UnOp::Not => rty::UnOp::Not,
        fhir::UnOp::Neg => rty::UnOp::Neg,
    }
}

fn def_id_to_param_ty(genv: GlobalEnv, def_id: DefId) -> rty::ParamTy {
    let def_kind = genv.tcx().def_kind(def_id);
    let name = match def_kind {
        DefKind::Trait | DefKind::TraitAlias => kw::SelfUpper,
        DefKind::LifetimeParam | DefKind::TyParam | DefKind::ConstParam => {
            genv.tcx().item_name(def_id)
        }
        _ => bug!("ty_param_name: {:?} is a {:?} not a type parameter", def_id, def_kind),
    };
    rty::ParamTy { index: genv.def_id_to_param_index(def_id), name }
}

mod errors {
    use flux_errors::E0999;
    use flux_macros::Diagnostic;
    use flux_middle::{fhir, global_env::GlobalEnv};
    use rustc_hir::def_id::DefId;
    use rustc_span::{symbol::Ident, Span};

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_assoc_type_not_found, code = E0999)]
    #[note]
    pub(super) struct AssocTypeNotFound {
        #[primary_span]
        #[label]
        span: Span,
    }

    impl AssocTypeNotFound {
        pub(super) fn new(assoc_ident: Ident) -> Self {
            Self { span: assoc_ident.span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_ambiguous_assoc_type, code = E0999)]
    pub(super) struct AmbiguousAssocType {
        #[primary_span]
        span: Span,
        name: Ident,
    }

    impl AmbiguousAssocType {
        pub(super) fn new(assoc_ident: Ident) -> Self {
            Self { span: assoc_ident.span, name: assoc_ident }
        }
    }

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_invalid_base_instance, code = E0999)]
    pub(super) struct InvalidBaseInstance {
        #[primary_span]
        span: Span,
    }

    impl InvalidBaseInstance {
        pub(super) fn new(span: Span) -> Self {
            Self { span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_generic_argument_count_mismatch, code = E0999)]
    pub(super) struct GenericArgCountMismatch {
        #[primary_span]
        #[label]
        span: Span,
        found: usize,
        expected: usize,
        def_descr: &'static str,
    }

    impl GenericArgCountMismatch {
        pub(super) fn new(
            genv: GlobalEnv,
            def_id: DefId,
            segment: &fhir::PathSegment,
            expected: usize,
        ) -> Self {
            GenericArgCountMismatch {
                span: segment.ident.span,
                found: segment.args.len(),
                expected,
                def_descr: genv.tcx().def_descr(def_id),
            }
        }
    }

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_too_few_generic_args, code = E0999)]
    pub(super) struct TooFewGenericArgs {
        #[primary_span]
        #[label]
        span: Span,
        found: usize,
        min: usize,
        def_descr: &'static str,
    }

    impl TooFewGenericArgs {
        pub(super) fn new(
            genv: GlobalEnv,
            def_id: DefId,
            segment: &fhir::PathSegment,
            min: usize,
        ) -> Self {
            Self {
                span: segment.ident.span,
                found: segment.args.len(),
                min,
                def_descr: genv.tcx().def_descr(def_id),
            }
        }
    }

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_too_many_generic_args, code = E0999)]
    pub(super) struct TooManyGenericArgs {
        #[primary_span]
        #[label]
        span: Span,
        found: usize,
        max: usize,
        def_descr: &'static str,
    }

    impl TooManyGenericArgs {
        pub(super) fn new(
            genv: GlobalEnv,
            def_id: DefId,
            segment: &fhir::PathSegment,
            max: usize,
        ) -> Self {
            Self {
                span: segment.ident.span,
                found: segment.args.len(),
                max,
                def_descr: genv.tcx().def_descr(def_id),
            }
        }
    }
}
