//! Conversion from types in [`fhir`] to types in [`rty`]
//!
//! Conversion assumes well-formedness and will panic if type are not well-formed. Among other things,
//! well-formedness implies:
//! 1. Names are bound correctly.
//! 2. Refinement parameters appear in allowed positions. This is particularly important for
//!    refinement predicates, aka abstract refinements, since the syntax in [`rty`] has
//!    syntactic restrictions on predicates.
//! 3. Refinements are well-sorted.
use std::{borrow::Borrow, iter};

use flux_common::{bug, iter::IterExt, span_bug};
use flux_middle::{
    fhir::{self, ExprRes, FhirId, SurfaceIdent},
    global_env::GlobalEnv,
    intern::List,
    queries::QueryResult,
    rty::{self, fold::TypeFoldable, refining, AdtSortDef, ESpan, WfckResults, INNERMOST},
    rustc::{self, lowering},
};
use itertools::Itertools;
use rustc_data_structures::fx::FxIndexMap;
use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
    PrimTy,
};
use rustc_middle::{
    middle::resolve_bound_vars::ResolvedArg,
    mir::Local,
    ty::{AssocItem, AssocKind, BoundVar},
};
use rustc_span::{symbol::kw, Span, Symbol};
use rustc_type_ir::DebruijnIndex;

pub struct ConvCtxt<'a, 'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    wfckresults: &'a WfckResults<'genv>,
}

pub(crate) struct Env {
    layers: Vec<Layer>,
    early_bound: FxIndexMap<fhir::ParamId, (Symbol, rty::Sort)>,
}

#[derive(Debug, Clone)]
struct Layer {
    map: FxIndexMap<fhir::ParamId, Entry>,
    /// Whether to skip variables bound to Unit in this layer.
    filter_unit: bool,
    kind: LayerKind,
}

#[derive(Debug, Clone, Copy)]
enum LayerKind {
    List,
    Record(DefId),
}

#[derive(Debug, Clone)]
enum Entry {
    Sort {
        infer_mode: rty::InferMode,
        name: Symbol,
        sort: rty::Sort,
        /// The index of the entry in the layer skipping all [`Entry::Unit`] if [`Layer::filter_unit`]
        /// is true
        idx: u32,
    },
    /// We track parameters of unit sort separately because we avoid creating bound variables for them
    /// in function signatures.
    Unit(Symbol),
}

#[derive(Debug)]
struct LookupResult<'a> {
    kind: LookupResultKind<'a>,
    /// The span of the variable that originated the lookup. Used to report bugs.
    span: Span,
}

#[derive(Debug)]
enum LookupResultKind<'a> {
    LateBound { level: u32, entry: &'a Entry, kind: LayerKind },
    EarlyParam { idx: u32, name: Symbol, sort: rty::Sort },
}

pub(crate) fn conv_adt_sort_def(
    genv: GlobalEnv,
    def_id: LocalDefId,
    refined_by: &fhir::RefinedBy,
) -> rty::AdtSortDef {
    let params = refined_by
        .sort_params
        .iter()
        .map(|def_id| genv.def_id_to_param_ty(def_id.expect_local()))
        .collect();
    let fields = refined_by
        .index_params
        .iter()
        .map(|(name, sort)| (*name, conv_sort(genv, sort, &mut bug_on_infer_sort)))
        .collect_vec();
    let def_id = genv
        .map()
        .extern_id_of(def_id)
        .unwrap_or(def_id.to_def_id());
    rty::AdtSortDef::new(def_id, params, fields)
}

pub(crate) fn expand_type_alias<'genv>(
    genv: GlobalEnv<'genv, '_>,
    alias: &fhir::TyAlias,
    wfckresults: &WfckResults<'genv>,
) -> QueryResult<rty::Binder<rty::Ty>> {
    let def_id = alias.owner_id.to_def_id();
    let cx = ConvCtxt::new(genv, wfckresults);

    let mut env = Env::new(genv, alias.generics.refinement_params, wfckresults);
    env.push_layer(Layer::record(&cx, def_id, alias.index_params));

    let ty = cx.conv_ty(&mut env, &alias.ty)?;
    Ok(rty::Binder::new(ty, env.pop_layer().into_bound_vars(genv)))
}

pub(crate) fn conv_generic_predicates<'genv>(
    genv: GlobalEnv<'genv, '_>,
    def_id: LocalDefId,
    predicates: &[fhir::WhereBoundPredicate],
    wfckresults: &WfckResults<'genv>,
) -> QueryResult<rty::EarlyBinder<rty::GenericPredicates>> {
    let cx = ConvCtxt::new(genv, wfckresults);

    let refparams = &genv.map().get_generics(def_id).unwrap().refinement_params;

    let env = &mut Env::new(genv, refparams, wfckresults);

    let mut clauses = vec![];
    for pred in predicates {
        let bounded_ty = cx.conv_ty(env, &pred.bounded_ty)?;
        for clause in cx.conv_generic_bounds(env, bounded_ty, pred.bounds)? {
            clauses.push(clause);
        }
    }
    let parent = genv.tcx().predicates_of(def_id.to_def_id()).parent;
    Ok(rty::EarlyBinder(rty::GenericPredicates { parent, predicates: List::from_vec(clauses) }))
}

pub(crate) fn conv_opaque_ty<'genv>(
    genv: GlobalEnv<'genv, '_>,
    def_id: LocalDefId,
    opaque_ty: &fhir::OpaqueTy,
    wfckresults: &WfckResults<'genv>,
) -> QueryResult<List<rty::Clause>> {
    let cx = ConvCtxt::new(genv, wfckresults);
    let parent = genv.tcx().local_parent(def_id);
    let refparams = &genv.map().get_generics(parent).unwrap().refinement_params;
    let parent_wfckresults = genv.check_wf(parent)?;

    let env = &mut Env::new(genv, refparams, &parent_wfckresults);

    let args = rty::GenericArgs::identity_for_item(genv, def_id)?;
    let self_ty = rty::Ty::opaque(def_id, args, env.to_early_bound_vars());
    Ok(cx
        .conv_generic_bounds(env, self_ty, opaque_ty.bounds)?
        .into_iter()
        .collect())
}

pub(crate) fn conv_generics(
    rust_generics: &rustc::ty::Generics,
    generics: &fhir::Generics,
    is_trait: Option<LocalDefId>,
) -> QueryResult<rty::Generics> {
    let opt_self = is_trait.map(|def_id| {
        let kind = generics
            .self_kind
            .as_ref()
            .map_or(rty::GenericParamDefKind::Type { has_default: false }, conv_generic_param_kind);
        rty::GenericParamDef { index: 0, name: kw::SelfUpper, def_id: def_id.to_def_id(), kind }
    });
    let params = opt_self
        .into_iter()
        .chain(rust_generics.params.iter().flat_map(|rust_param| {
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
        .collect();

    Ok(rty::Generics {
        params,
        parent: rust_generics.parent(),
        parent_count: rust_generics.parent_count(),
    })
}

pub(crate) fn conv_refinement_generics<'genv>(
    genv: GlobalEnv<'genv, '_>,
    params: &[fhir::RefineParam],
    wfckresults: Option<&WfckResults<'genv>>,
) -> List<rty::RefineParam> {
    params
        .iter()
        .map(|param| conv_refine_param(genv, param, wfckresults))
        .collect()
}

fn conv_generic_param_kind(kind: &fhir::GenericParamKind) -> rty::GenericParamDefKind {
    match kind {
        fhir::GenericParamKind::Type { default } => {
            rty::GenericParamDefKind::Type { has_default: default.is_some() }
        }
        fhir::GenericParamKind::Base => rty::GenericParamDefKind::Base,
        fhir::GenericParamKind::Lifetime => rty::GenericParamDefKind::Lifetime,
    }
}

pub(crate) fn adt_def_for_struct(
    genv: GlobalEnv,
    invariants: Vec<rty::Invariant>,
    struct_def: &fhir::StructDef,
) -> rty::AdtDef {
    let def_id = struct_def.owner_id.def_id;
    let adt_def = if let Some(extern_id) = struct_def.extern_id {
        lowering::lower_adt_def(&genv.tcx().adt_def(extern_id))
    } else {
        lowering::lower_adt_def(&genv.tcx().adt_def(struct_def.owner_id))
    };
    rty::AdtDef::new(adt_def, genv.adt_sort_def_of(def_id), invariants, struct_def.is_opaque())
}

pub(crate) fn adt_def_for_enum(
    genv: GlobalEnv,
    invariants: Vec<rty::Invariant>,
    enum_def: &fhir::EnumDef,
) -> rty::AdtDef {
    let def_id = enum_def.owner_id.def_id;
    let adt_def = if let Some(extern_id) = enum_def.extern_id {
        lowering::lower_adt_def(&genv.tcx().adt_def(extern_id))
    } else {
        lowering::lower_adt_def(&genv.tcx().adt_def(enum_def.owner_id))
    };
    rty::AdtDef::new(adt_def, genv.adt_sort_def_of(def_id), invariants, false)
}

pub(crate) fn conv_invariants<'genv>(
    genv: GlobalEnv<'genv, '_>,
    def_id: LocalDefId,
    params: &[fhir::RefineParam],
    invariants: &[fhir::Expr],
    wfckresults: &WfckResults<'genv>,
) -> QueryResult<Vec<rty::Invariant>> {
    let cx = ConvCtxt::new(genv, wfckresults);
    let mut env = Env::new(genv, &[], wfckresults);
    env.push_layer(Layer::record(&cx, def_id.to_def_id(), params));
    cx.conv_invariants(&mut env, invariants)
}

pub(crate) fn conv_defn<'genv>(
    genv: GlobalEnv<'genv, '_>,
    func: &fhir::SpecFunc,
    wfckresults: &WfckResults<'genv>,
) -> QueryResult<Option<rty::SpecFunc>> {
    if let Some(body) = &func.body {
        let cx = ConvCtxt::new(genv, wfckresults);
        let mut env = Env::new(genv, &[], wfckresults);
        env.push_layer(Layer::list(&cx, 0, func.args, false));
        let expr = cx.conv_expr(&mut env, body)?;
        let expr = rty::Binder::new(expr, env.pop_layer().into_bound_vars(genv));
        Ok(Some(rty::SpecFunc { name: func.name, expr }))
    } else {
        Ok(None)
    }
}

pub(crate) fn conv_qualifier<'genv>(
    genv: GlobalEnv<'genv, '_>,
    qualifier: &fhir::Qualifier,
    wfckresults: &WfckResults<'genv>,
) -> QueryResult<rty::Qualifier> {
    let cx = ConvCtxt::new(genv, wfckresults);
    let mut env = Env::new(genv, &[], wfckresults);
    env.push_layer(Layer::list(&cx, 0, qualifier.args, false));
    let body = cx.conv_expr(&mut env, &qualifier.expr)?;
    let body = rty::Binder::new(body, env.pop_layer().into_bound_vars(genv));
    Ok(rty::Qualifier { name: qualifier.name, body, global: qualifier.global })
}

pub(crate) fn conv_fn_decl<'genv>(
    genv: GlobalEnv<'genv, '_>,
    def_id: LocalDefId,
    decl: &fhir::FnDecl,
    wfckresults: &WfckResults<'genv>,
) -> QueryResult<rty::EarlyBinder<rty::PolyFnSig>> {
    let cx = ConvCtxt::new(genv, wfckresults);

    let late_bound_regions = refining::refine_bound_variables(&genv.lower_late_bound_vars(def_id)?);

    let mut env = Env::new(genv, decl.generics.refinement_params, wfckresults);
    env.push_layer(Layer::list(&cx, late_bound_regions.len() as u32, &[], true));

    let mut requires = vec![];
    for constr in decl.requires {
        requires.push(cx.conv_constr(&mut env, constr)?);
    }

    let mut args = vec![];
    for ty in decl.args {
        args.push(cx.conv_ty(&mut env, ty)?);
    }

    let output = cx.conv_fn_output(&mut env, &decl.output)?;

    let vars = late_bound_regions
        .iter()
        .chain(env.pop_layer().into_bound_vars(genv).iter())
        .cloned()
        .collect();

    let res = rty::PolyFnSig::new(rty::FnSig::new(requires, args, output), vars);
    Ok(rty::EarlyBinder(res))
}

pub(crate) fn conv_assoc_reft_def<'genv>(
    genv: GlobalEnv<'genv, '_>,
    assoc_reft: &fhir::ImplAssocReft,
    wfckresults: &WfckResults<'genv>,
) -> QueryResult<rty::Lambda> {
    let cx = ConvCtxt::new(genv, wfckresults);
    let mut env = Env::new(genv, &[], wfckresults);
    env.push_layer(Layer::list(&cx, 0, assoc_reft.params, false));
    let expr = cx.conv_expr(&mut env, &assoc_reft.body)?;
    let inputs = env.pop_layer().into_bound_vars(genv);
    let output = conv_sort(genv, &assoc_reft.output, &mut bug_on_infer_sort);
    Ok(rty::Lambda::with_vars(expr, inputs, output))
}

pub(crate) fn conv_ty<'genv>(
    genv: GlobalEnv<'genv, '_>,
    ty: &fhir::Ty,
    wfckresults: &WfckResults<'genv>,
) -> QueryResult<rty::Binder<rty::Ty>> {
    let mut env = Env::new(genv, &[], wfckresults);
    let ty = ConvCtxt::new(genv, wfckresults).conv_ty(&mut env, ty)?;
    Ok(rty::Binder::new(ty, List::empty()))
}

impl<'a, 'genv, 'tcx> ConvCtxt<'a, 'genv, 'tcx> {
    pub(crate) fn new(genv: GlobalEnv<'genv, 'tcx>, wfckresults: &'a WfckResults<'genv>) -> Self {
        Self { genv, wfckresults }
    }

    fn conv_generic_bounds(
        &self,
        env: &mut Env,
        bounded_ty: rty::Ty,
        bounds: fhir::GenericBounds,
    ) -> QueryResult<Vec<rty::Clause>> {
        let mut clauses = vec![];
        for bound in bounds {
            self.conv_generic_bound(env, &bounded_ty, bound, &mut clauses)?;
        }
        Ok(clauses)
    }

    fn conv_generic_bound(
        &self,
        env: &mut Env,
        bounded_ty: &rty::Ty,
        bound: &fhir::GenericBound,
        clauses: &mut Vec<rty::Clause>,
    ) -> QueryResult {
        match bound {
            fhir::GenericBound::Trait(trait_ref, fhir::TraitBoundModifier::None) => {
                let trait_id = trait_ref.trait_def_id();
                if let Some(closure_kind) = self.genv.tcx().fn_trait_kind_from_def_id(trait_id) {
                    self.conv_fn_bound(env, bounded_ty, trait_ref, closure_kind, clauses)
                } else {
                    let path = &trait_ref.trait_ref;
                    let params = &trait_ref.bound_generic_params;
                    self.conv_trait_bound(
                        env,
                        bounded_ty,
                        trait_id,
                        path.last_segment().args,
                        params,
                        clauses,
                    )?;
                    self.conv_type_bindings(
                        env,
                        bounded_ty,
                        trait_id,
                        path.last_segment().bindings,
                        clauses,
                    )
                }
            }
            // Maybe bounds are only supported for `?Sized`. The effect of the maybe bound is to
            // relax the default which is `Sized` to not have the `Sized` bound, so we just skip
            // it here.
            fhir::GenericBound::Trait(_, fhir::TraitBoundModifier::Maybe) => Ok(()),
            fhir::GenericBound::LangItemTrait(lang_item, _, bindings) => {
                let trait_def_id = self.genv.tcx().require_lang_item(*lang_item, None);
                self.conv_type_bindings(env, bounded_ty, trait_def_id, bindings, clauses)
            }
        }
    }

    fn conv_trait_bound(
        &self,
        env: &mut Env,
        bounded_ty: &rty::Ty,
        trait_id: DefId,
        args: &[fhir::GenericArg],
        params: &[fhir::GenericParam],
        clauses: &mut Vec<rty::Clause>,
    ) -> QueryResult {
        let mut into = vec![rty::GenericArg::Ty(bounded_ty.clone())];
        self.conv_generic_args_into(env, trait_id, args, &mut into)?;
        self.fill_generic_args_defaults(trait_id, &mut into)?;
        let trait_ref = rty::TraitRef { def_id: trait_id, args: into.into() };
        let pred = rty::TraitPredicate { trait_ref };
        let vars = params
            .iter()
            .map(|param| self.conv_trait_bound_generic_param(param))
            .try_collect_vec()?;
        clauses.push(rty::Clause::new(List::from_vec(vars), rty::ClauseKind::Trait(pred)));
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
                    .name(self.genv.hir().local_def_id_to_hir_id(def_id));
                let kind = rty::BoundRegionKind::BrNamed(def_id.to_def_id(), name);
                Ok(rty::BoundVariableKind::Region(kind))
            }
            fhir::GenericParamKind::Type { .. } | fhir::GenericParamKind::Base => {
                bug!("unexpected!")
            }
        }
    }

    fn conv_fn_bound(
        &self,
        env: &mut Env,
        self_ty: &rty::Ty,
        trait_ref: &fhir::PolyTraitRef,
        kind: rty::ClosureKind,
        clauses: &mut Vec<rty::Clause>,
    ) -> QueryResult<()> {
        let path = &trait_ref.trait_ref;
        let layer = Layer::list(self, trait_ref.bound_generic_params.len() as u32, &[], true);
        env.push_layer(layer);

        let pred = rty::FnTraitPredicate {
            self_ty: self_ty.clone(),
            tupled_args: self.conv_ty(env, path.last_segment().args[0].expect_type())?,
            output: self.conv_ty(env, &path.last_segment().bindings[0].term)?,
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

    fn conv_type_bindings(
        &self,
        env: &mut Env,
        bounded_ty: &rty::Ty,
        trait_def_id: DefId,
        bindings: &[fhir::TypeBinding],
        clauses: &mut Vec<rty::Clause>,
    ) -> QueryResult<()> {
        for binding in bindings {
            let assoc_item = self
                .trait_defines_associated_item_named(trait_def_id, AssocKind::Type, binding.ident)
                .ok_or_else(|| {
                    self.genv
                        .sess()
                        .emit_err(errors::AssocTypeNotFound::new(binding.ident))
                })?;
            let args = List::singleton(rty::GenericArg::Ty(bounded_ty.clone()));
            let refine_args = List::empty();
            let alias_ty = rty::AliasTy { def_id: assoc_item.def_id, args, refine_args };
            let kind = rty::ClauseKind::Projection(rty::ProjectionPredicate {
                projection_ty: alias_ty,
                term: self.conv_ty(env, &binding.term)?,
            });
            clauses.push(rty::Clause::new(List::empty(), kind));
        }
        Ok(())
    }

    fn trait_defines_associated_item_named(
        &self,
        trait_def_id: DefId,
        assoc_kind: AssocKind,
        assoc_name: SurfaceIdent,
    ) -> Option<&AssocItem> {
        self.genv
            .tcx()
            .associated_items(trait_def_id)
            .find_by_name_and_kind(self.genv.tcx(), assoc_name, assoc_kind, trait_def_id)
    }

    fn conv_fn_output(
        &self,
        env: &mut Env,
        output: &fhir::FnOutput,
    ) -> QueryResult<rty::Binder<rty::FnOutput>> {
        env.push_layer(Layer::list(self, 0, output.params, true));

        let ret = self.conv_ty(env, &output.ret)?;
        let ensures: List<rty::Constraint> = output
            .ensures
            .iter()
            .map(|constr| self.conv_constr(env, constr))
            .try_collect()?;
        let output = rty::FnOutput::new(ret, ensures);

        let vars = env.pop_layer().into_bound_vars(self.genv);
        Ok(rty::Binder::new(output, vars))
    }

    pub(crate) fn conv_enum_def_variants(
        genv: GlobalEnv<'genv, '_>,
        enum_def: &fhir::EnumDef,
        wfckresults: &WfckResults<'genv>,
    ) -> QueryResult<Vec<rty::PolyVariant>> {
        enum_def
            .variants
            .iter()
            .map(|variant_def| {
                ConvCtxt::conv_enum_variant(
                    genv,
                    enum_def.owner_id.to_def_id(),
                    variant_def,
                    wfckresults,
                )
            })
            .try_collect()
    }

    fn conv_enum_variant(
        genv: GlobalEnv<'genv, '_>,
        adt_def_id: DefId,
        variant: &fhir::VariantDef,
        wfckresults: &WfckResults<'genv>,
    ) -> QueryResult<rty::PolyVariant> {
        let cx = ConvCtxt::new(genv, wfckresults);

        let mut env = Env::new(genv, &[], wfckresults);
        env.push_layer(Layer::list(&cx, 0, variant.params, true));

        let adt_def = genv.adt_def(adt_def_id)?;
        let fields = variant
            .fields
            .iter()
            .map(|field| cx.conv_ty(&mut env, &field.ty))
            .try_collect()?;
        let idxs = cx.conv_refine_arg(&mut env, &variant.ret.idx)?;
        let variant = rty::VariantSig::new(
            adt_def,
            rty::GenericArgs::identity_for_item(genv, adt_def_id)?,
            fields,
            idxs,
        );

        Ok(rty::Binder::new(variant, env.pop_layer().into_bound_vars(genv)))
    }

    pub(crate) fn conv_struct_def_variant(
        genv: GlobalEnv<'genv, '_>,
        struct_def: &fhir::StructDef,
        wfckresults: &WfckResults<'genv>,
    ) -> QueryResult<rty::Opaqueness<rty::PolyVariant>> {
        let cx = ConvCtxt::new(genv, wfckresults);
        let mut env = Env::new(genv, &[], wfckresults);
        env.push_layer(Layer::list(&cx, 0, struct_def.params, false));

        let def_id = struct_def.owner_id.def_id;
        if let fhir::StructKind::Transparent { fields } = &struct_def.kind {
            let adt_def = genv.adt_def(def_id)?;

            let fields = fields
                .iter()
                .map(|field_def| cx.conv_ty(&mut env, &field_def.ty))
                .try_collect()?;

            let vars = env.pop_layer().into_bound_vars(genv);
            let idx = rty::Expr::adt(
                def_id.to_def_id(),
                (0..vars.len())
                    .map(|idx| {
                        rty::Expr::late_bvar(INNERMOST, idx as u32, rty::BoundReftKind::Annon)
                    })
                    .collect(),
            );
            let variant = rty::VariantSig::new(
                adt_def,
                rty::GenericArgs::identity_for_item(genv, def_id)?,
                fields,
                idx,
            );
            Ok(rty::Opaqueness::Transparent(rty::Binder::new(variant, vars)))
        } else {
            Ok(rty::Opaqueness::Opaque)
        }
    }

    fn conv_constr(
        &self,
        env: &mut Env,
        constr: &fhir::Constraint,
    ) -> QueryResult<rty::Constraint> {
        match constr {
            fhir::Constraint::Type(loc, ty) => {
                let (idx, _) = loc.res.expect_loc_param();
                Ok(rty::Constraint::Type(
                    env.lookup(loc).to_path(),
                    self.conv_ty(env, ty)?,
                    Local::from_usize(idx + 1),
                ))
            }
            fhir::Constraint::Pred(pred) => Ok(rty::Constraint::Pred(self.conv_expr(env, pred)?)),
        }
    }

    fn conv_alias_reft(
        &self,
        env: &mut Env,
        alias: &fhir::AliasReft,
        func_args: &[fhir::Expr],
    ) -> QueryResult<rty::Expr> {
        let trait_id = alias.trait_id;
        let generic_args = self
            .conv_generic_args(env, trait_id, alias.generic_args)?
            .into();
        let func_args = func_args
            .iter()
            .map(|arg| self.conv_expr(env, arg))
            .try_collect()?;
        let alias_reft = rty::AliasReft { trait_id, name: alias.name, args: generic_args };
        Ok(rty::Expr::alias(alias_reft, func_args))
    }

    fn conv_ty(&self, env: &mut Env, ty: &fhir::Ty) -> QueryResult<rty::Ty> {
        match &ty.kind {
            fhir::TyKind::BaseTy(bty) => self.conv_base_ty(env, bty),
            fhir::TyKind::Indexed(bty, idx) => {
                let idx = self.conv_refine_arg(env, idx)?;
                match &bty.kind {
                    fhir::BaseTyKind::Path(fhir::QPath::Resolved(_, path)) => {
                        Ok(self.conv_ty_ctor(env, path)?.replace_bound_reft(&idx))
                    }
                    fhir::BaseTyKind::Slice(ty) => {
                        let bty = rty::BaseTy::Slice(self.conv_ty(env, ty)?);
                        Ok(rty::Ty::indexed(bty, idx))
                    }
                }
            }
            fhir::TyKind::Exists(params, ty) => {
                let layer = Layer::list(self, 0, params, false);
                env.push_layer(layer);
                let ty = self.conv_ty(env, ty)?;
                let sorts = env.pop_layer().into_bound_vars(self.genv);
                if sorts.is_empty() {
                    Ok(ty.shift_out_escaping(1))
                } else {
                    Ok(rty::Ty::exists(rty::Binder::new(ty, sorts)))
                }
            }
            fhir::TyKind::Ptr(lft, loc) => {
                let region = self.conv_lifetime(env, *lft);
                Ok(rty::Ty::ptr(rty::PtrKind::Mut(region), env.lookup(loc).to_path()))
            }
            fhir::TyKind::Ref(lft, fhir::MutTy { ty, mutbl }) => {
                let region = self.conv_lifetime(env, *lft);
                Ok(rty::Ty::mk_ref(region, self.conv_ty(env, ty)?, *mutbl))
            }
            fhir::TyKind::Tuple(tys) => {
                let tys: List<rty::Ty> =
                    tys.iter().map(|ty| self.conv_ty(env, ty)).try_collect()?;
                Ok(rty::Ty::tuple(tys))
            }
            fhir::TyKind::Array(ty, len) => {
                Ok(rty::Ty::array(
                    self.conv_ty(env, ty)?,
                    rty::Const::from_array_len(self.genv.tcx(), len.val),
                ))
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
            fhir::TyKind::Hole(fhir_id) => {
                let ty = self
                    .wfckresults
                    .type_holes()
                    .get(*fhir_id)
                    .unwrap_or_else(|| span_bug!(ty.span, "unfilled type hole"));
                self.conv_ty(env, ty)
            }
            fhir::TyKind::OpaqueDef(item_id, args0, refine_args, _in_trait) => {
                let def_id = item_id.owner_id.to_def_id();
                let args = List::from_vec(self.conv_generic_args(env, def_id, args0)?);
                let refine_args = refine_args
                    .iter()
                    .map(|arg| self.conv_refine_arg(env, arg))
                    .try_collect()?;
                let alias_ty = rty::AliasTy::new(def_id, args, refine_args);
                Ok(rty::Ty::alias(rty::AliasKind::Opaque, alias_ty))
            }
        }
    }

    fn conv_base_ty(&self, env: &mut Env, bty: &fhir::BaseTy) -> QueryResult<rty::Ty> {
        match &bty.kind {
            fhir::BaseTyKind::Path(fhir::QPath::Resolved(self_ty, path)) => {
                match path.res {
                    fhir::Res::Def(DefKind::AssocTy, assoc_id) => {
                        let trait_id = self.genv.tcx().trait_of_item(assoc_id).unwrap();
                        let self_ty = self.conv_ty(env, self_ty.as_deref().unwrap())?;
                        let [.., trait_segment, assoc_segment] = path.segments else {
                            span_bug!(bty.span, "expected at least two segments");
                        };
                        let mut args = vec![rty::GenericArg::Ty(self_ty)];
                        self.conv_generic_args_into(env, trait_id, trait_segment.args, &mut args)?;
                        self.conv_generic_args_into(env, assoc_id, assoc_segment.args, &mut args)?;
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
                        let owner_id = self.genv.hir().ty_param_owner(def_id.expect_local());
                        let param_ty = self.genv.def_id_to_param_ty(def_id.expect_local());
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

    fn conv_lifetime(&self, env: &Env, lft: fhir::Lifetime) -> rty::Region {
        let res = match lft {
            fhir::Lifetime::Hole(fhir_id) => {
                *self
                    .wfckresults
                    .lifetime_holes()
                    .get(fhir_id)
                    .unwrap_or_else(|| bug!("unresolved lifetime hole"))
            }
            fhir::Lifetime::Resolved(res) => res,
        };
        let tcx = self.genv.tcx();
        let lifetime_name = |def_id| tcx.hir().name(tcx.hir().local_def_id_to_hir_id(def_id));
        match res {
            ResolvedArg::StaticLifetime => rty::ReStatic,
            ResolvedArg::EarlyBound(def_id) => {
                let index = self.genv.def_id_to_param_index(def_id.expect_local());
                let name = lifetime_name(def_id.expect_local());
                rty::ReEarlyBound(rty::EarlyBoundRegion { def_id, index, name })
            }
            ResolvedArg::LateBound(_, index, def_id) => {
                let depth = env.depth().checked_sub(1).unwrap();
                let name = lifetime_name(def_id.expect_local());
                let kind = rty::BoundRegionKind::BrNamed(def_id, name);
                let var = BoundVar::from_u32(index);
                let bound_region = rty::BoundRegion { var, kind };
                rty::ReLateBound(rustc::ty::DebruijnIndex::from_usize(depth), bound_region)
            }
            ResolvedArg::Free(scope, id) => {
                let name = lifetime_name(id.expect_local());
                let bound_region = rty::BoundRegionKind::BrNamed(id, name);
                rty::ReFree(rty::FreeRegion { scope, bound_region })
            }
            ResolvedArg::Error(_) => bug!("lifetime resolved to an error"),
        }
    }

    fn conv_refine_arg(&self, env: &mut Env, arg: &fhir::RefineArg) -> QueryResult<rty::Expr> {
        match &arg.kind {
            fhir::RefineArgKind::Expr(expr) => self.conv_expr(env, expr),
            fhir::RefineArgKind::Abs(params, body) => {
                let layer = Layer::list(self, 0, params, false);

                env.push_layer(layer);
                let pred = self.conv_expr(env, body)?;
                let inputs = env.pop_layer().into_bound_vars(self.genv);
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

    fn conv_ty_ctor(&self, env: &mut Env, path: &fhir::Path) -> QueryResult<rty::TyCtor> {
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
                let args = self.conv_generic_args(env, *did, path.last_segment().args)?;
                rty::BaseTy::adt(adt_def, args)
            }
            fhir::Res::Def(DefKind::TyParam, def_id) => {
                rty::BaseTy::Param(self.genv.def_id_to_param_ty(def_id.expect_local()))
            }
            fhir::Res::SelfTyParam { .. } => rty::BaseTy::Param(rty::SELF_PARAM_TY),
            fhir::Res::SelfTyAlias { alias_to, .. } => {
                return Ok(self.genv.type_of(*alias_to)?.instantiate_identity(&[]));
            }
            fhir::Res::Def(DefKind::TyAlias { .. }, def_id) => {
                let generics = self.conv_generic_args(env, *def_id, path.last_segment().args)?;
                let refine = path
                    .refine
                    .iter()
                    .map(|arg| self.conv_refine_arg(env, arg))
                    .try_collect_vec()?;
                return Ok(self.genv.type_of(*def_id)?.instantiate(&generics, &refine));
            }
            fhir::Res::Def(..) => {
                span_bug!(path.span, "unexpected resolution in conv_indexed_path: {:?}", path.res)
            }
        };
        let sort = bty.sort();
        let bty = bty.shift_in_escaping(1);
        Ok(rty::Binder::with_sort(rty::Ty::indexed(bty, rty::Expr::nu()), sort))
    }

    pub fn conv_generic_args(
        &self,
        env: &mut Env,
        def_id: DefId,
        args: &[fhir::GenericArg],
    ) -> QueryResult<Vec<rty::GenericArg>> {
        let mut into = vec![];
        self.conv_generic_args_into(env, def_id, args, &mut into)?;
        self.fill_generic_args_defaults(def_id, &mut into)?;
        Ok(into)
    }

    fn conv_generic_args_into(
        &self,
        env: &mut Env,
        def_id: DefId,
        args: &[fhir::GenericArg],
        into: &mut Vec<rty::GenericArg>,
    ) -> QueryResult {
        let generics = self.genv.generics_of(def_id)?;
        for (idx, arg) in args.iter().enumerate() {
            let param = generics.param_at(idx, self.genv)?;
            match (arg, &param.kind) {
                (fhir::GenericArg::Lifetime(lft), rty::GenericParamDefKind::Lifetime) => {
                    into.push(rty::GenericArg::Lifetime(self.conv_lifetime(env, *lft)));
                }
                (fhir::GenericArg::Type(ty), rty::GenericParamDefKind::Type { .. }) => {
                    into.push(rty::GenericArg::Ty(self.conv_ty(env, ty)?));
                }
                (fhir::GenericArg::Type(ty), rty::GenericParamDefKind::Base) => {
                    let ctor = self
                        .conv_ty(env, ty)?
                        .shallow_canonicalize()
                        .to_simple_ty_ctor()
                        .ok_or_else(|| {
                            self.genv
                                .sess()
                                .emit_err(errors::InvalidBaseInstance::new(ty))
                        })?;
                    into.push(rty::GenericArg::Base(ctor));
                }
                _ => {
                    bug!("unexpected param `{:?}` for arg `{arg:?}`", param.kind);
                }
            }
        }
        Ok(())
    }

    fn fill_generic_args_defaults(
        &self,
        def_id: DefId,
        into: &mut Vec<rty::GenericArg>,
    ) -> QueryResult {
        let generics = self.genv.generics_of(def_id)?;
        for param in generics.params.iter().skip(into.len()) {
            if let rty::GenericParamDefKind::Type { has_default } = param.kind {
                debug_assert!(has_default);
                let ty = self
                    .genv
                    .type_of(param.def_id)?
                    .instantiate(into, &[])
                    .to_ty();
                into.push(rty::GenericArg::Ty(ty));
            } else {
                bug!("unexpected generic param: {param:?}");
            }
        }

        Ok(())
    }

    fn resolve_param_sort(&self, param: &fhir::RefineParam) -> rty::Sort {
        resolve_param_sort(self.genv, param, Some(self.wfckresults)).clone()
    }
}

impl Env {
    pub(crate) fn new(
        genv: GlobalEnv,
        early_bound: &[fhir::RefineParam],
        wfckresults: &WfckResults,
    ) -> Self {
        let early_bound = early_bound
            .iter()
            .map(|param| {
                let sort = resolve_param_sort(genv, param, Some(wfckresults)).clone();
                (param.id, (param.name, sort))
            })
            .collect();
        Self { layers: vec![], early_bound }
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
        for (level, layer) in self.layers.iter().rev().enumerate() {
            if let Some(kind) = layer.get(id, level as u32) {
                return LookupResult { span: var.span, kind };
            }
        }
        if let Some((idx, _, (name, sort))) = self.early_bound.get_full(&id) {
            LookupResult {
                span: var.span,
                kind: LookupResultKind::EarlyParam {
                    idx: idx as u32,
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
    fn conv_expr(&self, env: &mut Env, expr: &fhir::Expr) -> QueryResult<rty::Expr> {
        let fhir_id = expr.fhir_id;
        let espan = Some(ESpan::new(expr.span));
        let expr = match &expr.kind {
            fhir::ExprKind::Var(var, _) => {
                match var.res {
                    ExprRes::Param(..) => env.lookup(var).to_expr(),
                    ExprRes::Const(def_id) => rty::Expr::const_def_id(def_id, espan),
                    ExprRes::NumConst(num) => {
                        rty::Expr::constant_at(rty::Constant::from(num), espan)
                    }
                    ExprRes::GlobalFunc(..) => {
                        span_bug!(var.span, "unexpected func in var position")
                    }
                }
            }
            fhir::ExprKind::Literal(lit) => rty::Expr::constant_at(conv_lit(*lit), espan),
            fhir::ExprKind::BinaryOp(op, e1, e2) => {
                rty::Expr::binary_op(
                    self.conv_bin_op(*op, expr.fhir_id),
                    self.conv_expr(env, e1)?,
                    self.conv_expr(env, e2)?,
                    espan,
                )
            }
            fhir::ExprKind::UnaryOp(op, e) => {
                rty::Expr::unary_op(conv_un_op(*op), self.conv_expr(env, e)?, espan)
            }
            fhir::ExprKind::App(func, args) => {
                rty::Expr::app(self.conv_func(env, func), self.conv_exprs(env, args)?, espan)
            }
            fhir::ExprKind::Alias(alias, func_args) => {
                self.conv_alias_reft(env, alias, func_args)?
            }
            fhir::ExprKind::IfThenElse(p, e1, e2) => {
                rty::Expr::ite(
                    self.conv_expr(env, p)?,
                    self.conv_expr(env, e1)?,
                    self.conv_expr(env, e2)?,
                    espan,
                )
            }
            fhir::ExprKind::Dot(var, fld) => env.lookup(var).get_field(*fld),
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

    fn conv_exprs(&self, env: &mut Env, exprs: &[fhir::Expr]) -> QueryResult<List<rty::Expr>> {
        exprs.iter().map(|e| self.conv_expr(env, e)).collect()
    }

    fn conv_invariants(
        &self,
        env: &mut Env,
        invariants: &[fhir::Expr],
    ) -> QueryResult<Vec<rty::Invariant>> {
        invariants
            .iter()
            .map(|invariant| self.conv_invariant(env, invariant))
            .collect()
    }

    fn conv_invariant(&self, env: &mut Env, invariant: &fhir::Expr) -> QueryResult<rty::Invariant> {
        Ok(rty::Invariant::new(rty::Binder::new(
            self.conv_expr(env, invariant)?,
            env.top_layer().to_bound_vars(self.genv),
        )))
    }

    fn add_coercions(&self, mut expr: rty::Expr, fhir_id: FhirId) -> rty::Expr {
        let span = expr.span();
        if let Some(coercions) = self.wfckresults.coercions().get(fhir_id) {
            for coercion in coercions {
                expr = match *coercion {
                    rty::Coercion::Inject(def_id) => rty::Expr::adt(def_id, List::singleton(expr)),
                    rty::Coercion::Project(def_id) => {
                        rty::Expr::field_proj(expr, rty::FieldProj::Adt { def_id, field: 0 }, span)
                    }
                };
            }
        }
        expr
    }
}

impl Layer {
    fn new(
        cx: &ConvCtxt,
        late_bound_regions: u32,
        params: &[fhir::RefineParam],
        filter_unit: bool,
        kind: LayerKind,
    ) -> Self {
        let mut idx = late_bound_regions;
        let map = params
            .iter()
            .map(|param| {
                let sort = cx.resolve_param_sort(param);
                let infer_mode = sort.infer_mode(param.kind);
                let entry = Entry::new(idx, sort, infer_mode, param.name);
                if !filter_unit || !matches!(entry, Entry::Unit(_)) {
                    idx += 1;
                }
                (param.id, entry)
            })
            .collect();
        Self { map, filter_unit, kind }
    }

    fn list(
        cx: &ConvCtxt,
        late_bound_regions: u32,
        params: &[fhir::RefineParam],
        filter_unit: bool,
    ) -> Self {
        Self::new(cx, late_bound_regions, params, filter_unit, LayerKind::List)
    }

    fn record(cx: &ConvCtxt, def_id: DefId, params: &[fhir::RefineParam]) -> Self {
        Self::new(cx, 0, params, false, LayerKind::Record(def_id))
    }

    fn get(&self, name: impl Borrow<fhir::ParamId>, level: u32) -> Option<LookupResultKind> {
        Some(LookupResultKind::LateBound {
            level,
            entry: self.map.get(name.borrow())?,
            kind: self.kind,
        })
    }

    fn into_bound_vars(self, genv: GlobalEnv) -> List<rty::BoundVariableKind> {
        match self.kind {
            LayerKind::List => {
                self.into_iter()
                    .map(|(sort, mode, name)| {
                        let kind = rty::BoundReftKind::Named(name);
                        rty::BoundVariableKind::Refine(sort, mode, kind)
                    })
                    .collect()
            }
            LayerKind::Record(def_id) => {
                let sort_def = genv.adt_sort_def_of(def_id);
                let args = sort_def.identity_args();
                let ctor = rty::SortCtor::Adt(sort_def);
                let sort = rty::Sort::App(ctor, args);
                let infer_mode = sort.default_infer_mode();
                let kind = rty::BoundReftKind::Annon;
                List::singleton(rty::BoundVariableKind::Refine(sort, infer_mode, kind))
            }
        }
    }

    fn to_bound_vars(&self, genv: GlobalEnv) -> List<rty::BoundVariableKind> {
        self.clone().into_bound_vars(genv)
    }

    fn into_iter(self) -> impl Iterator<Item = (rty::Sort, rty::InferMode, Symbol)> {
        self.map.into_values().filter_map(move |entry| {
            match entry {
                Entry::Sort { infer_mode, sort, name, .. } => Some((sort, infer_mode, name)),
                Entry::Unit(name) => {
                    if self.filter_unit {
                        None
                    } else {
                        let unit = rty::Sort::unit();
                        let infer_mode = unit.default_infer_mode();
                        Some((unit, infer_mode, name))
                    }
                }
            }
        })
    }
}

impl Entry {
    fn new(idx: u32, sort: rty::Sort, infer_mode: fhir::InferMode, name: Symbol) -> Self {
        if sort.is_unit() {
            Entry::Unit(name)
        } else {
            Entry::Sort { sort, infer_mode, idx, name }
        }
    }
}

impl LookupResult<'_> {
    fn to_expr(&self) -> rty::Expr {
        match &self.kind {
            LookupResultKind::LateBound { level, entry: Entry::Sort { idx, name, .. }, kind } => {
                match *kind {
                    LayerKind::List => {
                        rty::Expr::late_bvar(
                            DebruijnIndex::from_u32(*level),
                            *idx,
                            rty::BoundReftKind::Named(*name),
                        )
                    }
                    LayerKind::Record(def_id) => {
                        rty::Expr::field_proj(
                            rty::Expr::late_bvar(
                                DebruijnIndex::from_u32(*level),
                                0,
                                rty::BoundReftKind::Annon,
                            ),
                            rty::FieldProj::Adt { def_id, field: *idx },
                            None,
                        )
                    }
                }
            }
            LookupResultKind::LateBound { entry: Entry::Unit(_), .. } => rty::Expr::unit(),
            LookupResultKind::EarlyParam { idx, name, .. } => rty::Expr::early_param(*idx, *name),
        }
    }

    fn is_adt(&self) -> Option<&AdtSortDef> {
        match &self.kind {
            LookupResultKind::LateBound {
                entry: Entry::Sort { sort: rty::Sort::App(rty::SortCtor::Adt(sort_def), _), .. },
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
        self.to_expr()
            .to_path()
            .unwrap_or_else(|| span_bug!(self.span, "expected path, found `{:?}`", self.to_expr()))
    }

    fn get_field(&self, fld: SurfaceIdent) -> rty::Expr {
        if let Some(sort_def) = self.is_adt() {
            let def_id = sort_def.did();
            let i = sort_def
                .field_index(fld.name)
                .unwrap_or_else(|| span_bug!(fld.span, "field `{fld:?}` not found in {def_id:?}"));
            rty::Expr::field_proj(
                self.to_expr(),
                rty::FieldProj::Adt { def_id, field: i as u32 },
                None,
            )
        } else {
            span_bug!(fld.span, "expected adt sort")
        }
    }
}

pub fn conv_func_decl(genv: GlobalEnv, func: &fhir::SpecFunc) -> rty::SpecFuncDecl {
    let inputs_and_output = func
        .args
        .iter()
        .map(|p| &p.sort)
        .chain(iter::once(&func.sort))
        .map(|sort| conv_sort(genv, sort, &mut bug_on_infer_sort))
        .collect();
    let sort = rty::PolyFuncSort::new(func.params, rty::FuncSort { inputs_and_output });
    let kind = if func.body.is_some() { fhir::SpecFuncKind::Def } else { fhir::SpecFuncKind::Uif };
    rty::SpecFuncDecl { name: func.name, sort, kind }
}

fn conv_sorts(
    genv: GlobalEnv,
    sorts: &[fhir::Sort],
    next_infer_sort: &mut impl FnMut() -> rty::Sort,
) -> Vec<rty::Sort> {
    sorts
        .iter()
        .map(|sort| conv_sort(genv, sort, next_infer_sort))
        .collect()
}

fn conv_refine_param(
    genv: GlobalEnv,
    param: &fhir::RefineParam,
    wfckresults: Option<&WfckResults>,
) -> rty::RefineParam {
    let sort = resolve_param_sort(genv, param, wfckresults);
    let mode = sort.infer_mode(param.kind);
    rty::RefineParam { sort, mode }
}

pub(crate) fn resolve_param_sort(
    genv: GlobalEnv,
    param: &fhir::RefineParam,
    wfckresults: Option<&WfckResults>,
) -> rty::Sort {
    if let fhir::Sort::Infer = &param.sort {
        wfckresults
            .expect("`Sort::Infer` without wfckresults")
            .node_sorts()
            .get(param.fhir_id)
            .unwrap_or_else(|| bug!("unresolved sort for param: `{param:?}`"))
            .clone()
    } else {
        conv_sort(genv, &param.sort, &mut bug_on_infer_sort)
    }
}

pub(crate) fn conv_sort(
    genv: GlobalEnv,
    sort: &fhir::Sort,
    next_infer_sort: &mut impl FnMut() -> rty::Sort,
) -> rty::Sort {
    match sort {
        fhir::Sort::Path(path) => conv_sort_path(genv, path, next_infer_sort),
        fhir::Sort::BitVec(w) => rty::Sort::BitVec(*w),
        fhir::Sort::Loc => rty::Sort::Loc,
        fhir::Sort::Func(fsort) => {
            rty::Sort::Func(conv_poly_func_sort(genv, fsort, next_infer_sort))
        }
        fhir::Sort::Infer => next_infer_sort(),
    }
}

fn conv_sort_path(
    genv: GlobalEnv,
    path: &fhir::SortPath,
    next_infer_sort: &mut impl FnMut() -> rty::Sort,
) -> rty::Sort {
    let ctor = match path.res {
        fhir::SortRes::PrimSort(fhir::PrimSort::Int) => return rty::Sort::Int,
        fhir::SortRes::PrimSort(fhir::PrimSort::Bool) => return rty::Sort::Bool,
        fhir::SortRes::PrimSort(fhir::PrimSort::Real) => return rty::Sort::Real,
        fhir::SortRes::SortParam(n) => return rty::Sort::Var(rty::ParamSort::from(n)),
        fhir::SortRes::TyParam(def_id) => {
            return rty::Sort::Param(genv.def_id_to_param_ty(def_id.expect_local()))
        }
        fhir::SortRes::SelfParam { .. } => return rty::Sort::Param(rty::SELF_PARAM_TY),
        fhir::SortRes::SelfAlias { alias_to } => {
            return genv
                .sort_of_self_ty_alias(alias_to)
                .unwrap_or(rty::Sort::Err)
        }
        fhir::SortRes::PrimSort(fhir::PrimSort::Set) => rty::SortCtor::Set,
        fhir::SortRes::PrimSort(fhir::PrimSort::Map) => rty::SortCtor::Map,
        fhir::SortRes::User { name } => rty::SortCtor::User { name },
        fhir::SortRes::Adt(def_id) => {
            let sort_def = genv.adt_sort_def_of(def_id);
            rty::SortCtor::Adt(sort_def)
        }
    };
    let args = path
        .args
        .iter()
        .map(|t| conv_sort(genv, t, next_infer_sort))
        .collect_vec();
    rty::Sort::app(ctor, args)
}

fn conv_poly_func_sort(
    genv: GlobalEnv,
    sort: &fhir::PolyFuncSort,
    next_infer_sort: &mut impl FnMut() -> rty::Sort,
) -> rty::PolyFuncSort {
    rty::PolyFuncSort::new(sort.params, conv_func_sort(genv, &sort.fsort, next_infer_sort))
}

pub(crate) fn conv_func_sort(
    genv: GlobalEnv,
    fsort: &fhir::FuncSort,
    next_infer_sort: &mut impl FnMut() -> rty::Sort,
) -> rty::FuncSort {
    rty::FuncSort::new(
        conv_sorts(genv, fsort.inputs(), next_infer_sort),
        conv_sort(genv, fsort.output(), next_infer_sort),
    )
}

fn conv_lit(lit: fhir::Lit) -> rty::Constant {
    match lit {
        fhir::Lit::Int(n) => rty::Constant::from(n),
        fhir::Lit::Real(r) => rty::Constant::Real(r),
        fhir::Lit::Bool(b) => rty::Constant::from(b),
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

mod errors {
    use flux_macros::Diagnostic;
    use flux_middle::fhir::{self, SurfaceIdent};
    use rustc_span::Span;

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_assoc_type_not_found, code = "FLUX")]
    #[note]
    pub(super) struct AssocTypeNotFound {
        #[primary_span]
        #[label]
        span: Span,
    }

    impl AssocTypeNotFound {
        pub(super) fn new(ident: SurfaceIdent) -> Self {
            Self { span: ident.span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_invalid_base_instance, code = "FLUX")]
    pub(super) struct InvalidBaseInstance<'fhir> {
        #[primary_span]
        span: Span,
        ty: &'fhir fhir::Ty<'fhir>,
    }

    impl<'fhir> InvalidBaseInstance<'fhir> {
        pub(super) fn new(ty: &'fhir fhir::Ty<'fhir>) -> Self {
            Self { ty, span: ty.span }
        }
    }
}
