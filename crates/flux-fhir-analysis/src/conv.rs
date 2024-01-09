//! Conversion from types in [`fhir`] to types in [`rty`]
//!
//! Conversion assumes well-formedness and will panic if type are not well-formed. Among other things,
//! well-formedness implies:
//! 1. Names are bound correctly.
//! 2. Refinement parameters appear in allowed positions. This is particularly important for
//!    refinement predicates, aka abstract refinements, since the syntax in [`rty`] has
//!    syntactic restrictions on predicates.
//! 3. Refinements are well-sorted.
use std::borrow::Borrow;

use flux_common::{bug, iter::IterExt, span_bug};
use flux_middle::{
    fhir::{self, FhirId, SurfaceIdent},
    global_env::GlobalEnv,
    intern::List,
    queries::QueryResult,
    rty::{self, fold::TypeFoldable, refining, ESpan, INNERMOST},
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
    ty::{AssocItem, AssocKind, BoundVar, TyCtxt},
};
use rustc_span::symbol::kw;
use rustc_type_ir::DebruijnIndex;

pub struct ConvCtxt<'a, 'tcx> {
    genv: &'a GlobalEnv<'a, 'tcx>,
    wfckresults: &'a fhir::WfckResults,
}

struct Env {
    layers: Vec<Layer>,
    early_bound: FxIndexMap<fhir::Name, fhir::Sort>,
}

#[derive(Debug, Clone)]
struct Layer {
    map: FxIndexMap<fhir::Name, Entry>,
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
        sort: fhir::Sort,
        infer_mode: rty::InferMode,
        conv: rty::Sort,
        /// The index of the entry in the layer skipping all [`Entry::Unit`] if [`Layer::filter_unit`]
        /// is true
        idx: u32,
    },
    /// We track parameters of unit sort separately because we avoid creating bound variables for them
    /// in function signatures.
    Unit,
}

#[derive(Debug)]
struct LookupResult<'a> {
    name: fhir::Ident,
    kind: LookupResultKind<'a>,
}

#[derive(Debug)]
enum LookupResultKind<'a> {
    LateBoundList { level: u32, entry: &'a Entry, kind: LayerKind },
    EarlyBound { idx: u32, sort: &'a fhir::Sort },
}

pub(crate) fn conv_adt_sort_def(genv: &GlobalEnv, refined_by: &fhir::RefinedBy) -> rty::AdtSortDef {
    let sorts = conv_sorts(genv, refined_by.index_sorts_raw());
    let params = refined_by
        .sort_params
        .iter()
        .map(|def_id| def_id_to_param_index(genv.tcx, def_id.expect_local()))
        .collect();
    let def_id = genv
        .map()
        .extern_id_of(genv.tcx, refined_by.def_id)
        .unwrap_or(refined_by.def_id.to_def_id());
    rty::AdtSortDef::new(def_id, params, List::from_vec(sorts))
}

pub(crate) fn expand_type_alias(
    genv: &GlobalEnv,
    alias: &fhir::TyAlias,
    wfckresults: &fhir::WfckResults,
) -> QueryResult<rty::Binder<rty::Ty>> {
    let def_id = alias.owner_id.to_def_id();
    let cx = ConvCtxt::new(genv, wfckresults);

    let mut env = Env::new(&alias.early_bound_params, wfckresults);
    env.push_layer(Layer::record(&cx, def_id, &alias.index_params));

    let ty = cx.conv_ty(&mut env, &alias.ty)?;
    Ok(rty::Binder::new(ty, env.pop_layer().into_bound_vars(genv)))
}

pub(crate) fn conv_generic_predicates(
    genv: &GlobalEnv,
    def_id: LocalDefId,
    predicates: &fhir::GenericPredicates,
    wfckresults: &fhir::WfckResults,
) -> QueryResult<rty::EarlyBinder<rty::GenericPredicates>> {
    let cx = ConvCtxt::new(genv, wfckresults);

    let refparams = genv.map().get_refine_params(genv.tcx, def_id);

    let env = &mut Env::new(refparams.unwrap_or(&[]), wfckresults);

    let mut clauses = vec![];
    for pred in &predicates.predicates {
        let bounded_ty = cx.conv_ty(env, &pred.bounded_ty)?;
        for clause in cx.conv_generic_bounds(env, bounded_ty, &pred.bounds)? {
            clauses.push(clause);
        }
    }
    let parent = genv.tcx.opt_parent(def_id.to_def_id());
    Ok(rty::EarlyBinder(rty::GenericPredicates { parent, predicates: List::from_vec(clauses) }))
}

pub(crate) fn conv_opaque_ty(
    genv: &GlobalEnv,
    def_id: LocalDefId,
    opaque_ty: &fhir::OpaqueTy,
    wfckresults: &fhir::WfckResults,
) -> QueryResult<List<rty::Clause>> {
    let cx = ConvCtxt::new(genv, wfckresults);
    let parent = genv.tcx.local_parent(def_id);
    let refparams = genv.map().get_refine_params(genv.tcx, parent);
    let parent_wfckresults = genv.check_wf(parent)?;

    let env = &mut Env::new(refparams.unwrap_or(&[]), &parent_wfckresults);

    let args = rty::GenericArgs::identity_for_item(genv, def_id)?;
    let self_ty = rty::Ty::opaque(def_id, args, env.to_early_bound_vars());
    Ok(cx
        .conv_generic_bounds(env, self_ty, &opaque_ty.bounds)?
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

pub(crate) fn conv_refinement_generics(
    genv: &GlobalEnv,
    params: &[fhir::RefineParam],
    wfckresults: &fhir::WfckResults,
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
        fhir::GenericParamKind::SplTy => rty::GenericParamDefKind::SplTy,
        fhir::GenericParamKind::BaseTy => rty::GenericParamDefKind::BaseTy,
        fhir::GenericParamKind::Lifetime => rty::GenericParamDefKind::Lifetime,
    }
}

pub(crate) fn adt_def_for_struct(
    genv: &GlobalEnv,
    invariants: Vec<rty::Invariant>,
    struct_def: &fhir::StructDef,
) -> rty::AdtDef {
    let def_id = struct_def.owner_id.def_id;
    let adt_def = if let Some(extern_id) = struct_def.extern_id {
        lowering::lower_adt_def(&genv.tcx.adt_def(extern_id))
    } else {
        lowering::lower_adt_def(&genv.tcx.adt_def(struct_def.owner_id))
    };
    rty::AdtDef::new(adt_def, genv.adt_sort_def_of(def_id), invariants, struct_def.is_opaque())
}

pub(crate) fn adt_def_for_enum(
    genv: &GlobalEnv,
    invariants: Vec<rty::Invariant>,
    enum_def: &fhir::EnumDef,
) -> rty::AdtDef {
    let def_id = enum_def.owner_id.def_id;
    let adt_def = if let Some(extern_id) = enum_def.extern_id {
        lowering::lower_adt_def(&genv.tcx.adt_def(extern_id))
    } else {
        lowering::lower_adt_def(&genv.tcx.adt_def(enum_def.owner_id))
    };
    rty::AdtDef::new(adt_def, genv.adt_sort_def_of(def_id), invariants, false)
}

pub(crate) fn conv_invariants(
    genv: &GlobalEnv,
    def_id: LocalDefId,
    params: &[fhir::RefineParam],
    invariants: &[fhir::Expr],
    wfckresults: &fhir::WfckResults,
) -> Vec<rty::Invariant> {
    let cx = ConvCtxt::new(genv, wfckresults);
    let mut env = Env::new(&[], wfckresults);
    env.push_layer(Layer::record(&cx, def_id.to_def_id(), params));
    cx.conv_invariants(&env, invariants)
}

pub(crate) fn conv_defn(
    genv: &GlobalEnv,
    defn: &fhir::Defn,
    wfckresults: &fhir::WfckResults,
) -> rty::Defn {
    let cx = ConvCtxt::new(genv, wfckresults);
    let mut env = Env::new(&[], wfckresults);
    env.push_layer(Layer::list(&cx, 0, &defn.args, false));
    let expr = cx.conv_expr(&env, &defn.expr);
    let expr = rty::Binder::new(expr, env.pop_layer().into_bound_vars(genv));
    rty::Defn { name: defn.name, expr }
}

pub(crate) fn conv_qualifier(
    genv: &GlobalEnv,
    qualifier: &fhir::Qualifier,
    wfckresults: &fhir::WfckResults,
) -> rty::Qualifier {
    let cx = ConvCtxt::new(genv, wfckresults);
    let mut env = Env::new(&[], wfckresults);
    env.push_layer(Layer::list(&cx, 0, &qualifier.args, false));
    let body = cx.conv_expr(&env, &qualifier.expr);
    let body = rty::Binder::new(body, env.pop_layer().into_bound_vars(genv));
    rty::Qualifier { name: qualifier.name, body, global: qualifier.global }
}

pub(crate) fn conv_fn_sig(
    genv: &GlobalEnv,
    def_id: LocalDefId,
    fn_sig: &fhir::FnSig,
    wfckresults: &fhir::WfckResults,
) -> QueryResult<rty::EarlyBinder<rty::PolyFnSig>> {
    let cx = ConvCtxt::new(genv, wfckresults);

    let late_bound_regions = refining::refine_bound_variables(&genv.lower_late_bound_vars(def_id)?);

    let mut env = Env::new(&fn_sig.params, wfckresults);
    env.push_layer(Layer::list(&cx, late_bound_regions.len() as u32, &[], true));

    let mut requires = vec![];
    for constr in &fn_sig.requires {
        requires.push(cx.conv_constr(&mut env, constr)?);
    }

    let mut args = vec![];
    for ty in &fn_sig.args {
        args.push(cx.conv_ty(&mut env, ty)?);
    }

    let output = cx.conv_fn_output(&mut env, &fn_sig.output)?;

    let vars = late_bound_regions
        .iter()
        .chain(env.pop_layer().into_bound_vars(genv).iter())
        .cloned()
        .collect();

    let res = rty::PolyFnSig::new(rty::FnSig::new(requires, args, output), vars);
    Ok(rty::EarlyBinder(res))
}

pub(crate) fn conv_ty(
    genv: &GlobalEnv,
    ty: &fhir::Ty,
    wfckresults: &fhir::WfckResults,
) -> QueryResult<rty::Binder<rty::Ty>> {
    let mut env = Env::new(&[], wfckresults);
    let ty = ConvCtxt::new(genv, wfckresults).conv_ty(&mut env, ty)?;
    Ok(rty::Binder::new(ty, List::empty()))
}

impl<'a, 'tcx> ConvCtxt<'a, 'tcx> {
    fn new(genv: &'a GlobalEnv<'a, 'tcx>, wfckresults: &'a fhir::WfckResults) -> Self {
        Self { genv, wfckresults }
    }

    fn conv_generic_bounds(
        &self,
        env: &mut Env,
        bounded_ty: rty::Ty,
        bounds: &fhir::GenericBounds,
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
    ) -> QueryResult<()> {
        match bound {
            fhir::GenericBound::Trait(trait_ref, fhir::TraitBoundModifier::None) => {
                let trait_id = trait_ref.trait_def_id();
                if let Some(closure_kind) = self.genv.tcx.fn_trait_kind_from_def_id(trait_id) {
                    self.conv_fn_bound(env, bounded_ty, trait_ref, closure_kind, clauses)
                } else {
                    let path = &trait_ref.trait_ref;
                    let params = &trait_ref.bound_generic_params;
                    self.conv_trait_bound(env, bounded_ty, trait_id, &path.args, params, clauses)?;
                    self.conv_type_bindings(env, bounded_ty, trait_id, &path.bindings, clauses)
                }
            }
            // Maybe bounds are only supported for `?Sized`. The effect of the maybe bound is to
            // relax the default which is `Sized` to not have the `Sized` bound, so we just skip
            // it here.
            fhir::GenericBound::Trait(_, fhir::TraitBoundModifier::Maybe) => Ok(()),
            fhir::GenericBound::LangItemTrait(lang_item, _, bindings) => {
                let trait_def_id = self.genv.tcx.require_lang_item(*lang_item, None);
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
    ) -> QueryResult<()> {
        let mut into = vec![rty::GenericArg::Ty(bounded_ty.clone())];
        self.conv_generic_args_into(env, args, &mut into)?;
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
                    .tcx
                    .hir()
                    .name(self.genv.tcx.hir().local_def_id_to_hir_id(def_id));
                let kind = rty::BoundRegionKind::BrNamed(def_id.to_def_id(), name);
                Ok(rty::BoundVariableKind::Region(kind))
            }
            fhir::GenericParamKind::Type { default: _ }
            | fhir::GenericParamKind::BaseTy
            | fhir::GenericParamKind::SplTy => bug!("unexpected!"),
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
            tupled_args: self.conv_ty(env, path.args[0].expect_type())?,
            output: self.conv_ty(env, &path.bindings[0].term)?,
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
                        .sess
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
            .tcx
            .associated_items(trait_def_id)
            .find_by_name_and_kind(self.genv.tcx, assoc_name, assoc_kind, trait_def_id)
    }

    fn conv_fn_output(
        &self,
        env: &mut Env,
        output: &fhir::FnOutput,
    ) -> QueryResult<rty::Binder<rty::FnOutput>> {
        env.push_layer(Layer::list(self, 0, &output.params, true));

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
        genv: &GlobalEnv,
        enum_def: &fhir::EnumDef,
        wfckresults: &fhir::WfckResults,
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
        genv: &GlobalEnv,
        adt_def_id: DefId,
        variant: &fhir::VariantDef,
        wfckresults: &fhir::WfckResults,
    ) -> QueryResult<rty::PolyVariant> {
        let cx = ConvCtxt::new(genv, wfckresults);

        let mut env = Env::new(&[], wfckresults);
        env.push_layer(Layer::list(&cx, 0, &variant.params, true));

        let adt_def = genv.adt_def(adt_def_id)?;
        let fields = variant
            .fields
            .iter()
            .map(|field| cx.conv_ty(&mut env, &field.ty))
            .try_collect()?;
        let idxs = cx.conv_refine_arg(&mut env, &variant.ret.idx);
        let variant = rty::VariantSig::new(
            adt_def,
            rty::GenericArgs::identity_for_item(genv, adt_def_id)?,
            fields,
            idxs,
        );

        Ok(rty::Binder::new(variant, env.pop_layer().into_bound_vars(genv)))
    }

    pub(crate) fn conv_struct_def_variant(
        genv: &GlobalEnv,
        struct_def: &fhir::StructDef,
        wfckresults: &fhir::WfckResults,
    ) -> QueryResult<rty::Opaqueness<rty::PolyVariant>> {
        let cx = ConvCtxt::new(genv, wfckresults);
        let mut env = Env::new(&[], wfckresults);
        env.push_layer(Layer::list(&cx, 0, &struct_def.params, false));

        let def_id = struct_def.owner_id.def_id;
        if let fhir::StructKind::Transparent { fields } = &struct_def.kind {
            let adt_def = genv.adt_def(def_id)?;

            let fields = fields
                .iter()
                .map(|field_def| cx.conv_ty(&mut env, &field_def.ty))
                .try_collect()?;

            let vars = env.pop_layer().into_bound_vars(genv);
            let idx = rty::Expr::record(
                def_id.to_def_id(),
                (0..vars.len())
                    .map(|idx| rty::Expr::late_bvar(INNERMOST, idx as u32))
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
            fhir::Constraint::Type(loc, ty, idx) => {
                Ok(rty::Constraint::Type(
                    env.lookup(*loc).to_path(),
                    self.conv_ty(env, ty)?,
                    Local::from_usize(*idx),
                ))
            }
            fhir::Constraint::Pred(pred) => Ok(rty::Constraint::Pred(self.conv_expr(env, pred))),
        }
    }

    fn conv_ty(&self, env: &mut Env, ty: &fhir::Ty) -> QueryResult<rty::Ty> {
        match &ty.kind {
            fhir::TyKind::BaseTy(bty) => self.conv_base_ty(env, bty),
            fhir::TyKind::Indexed(bty, idx) => {
                let idx = self.conv_refine_arg(env, idx);
                self.conv_indexed_type(env, bty, idx)
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
                Ok(rty::Ty::ptr(rty::PtrKind::Mut(region), env.lookup(*loc).to_path()))
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
                    rty::Const::from_array_len(self.genv.tcx, len.val),
                ))
            }
            fhir::TyKind::Never => Ok(rty::Ty::never()),
            fhir::TyKind::Constr(pred, ty) => {
                let pred = self.conv_expr(env, pred);
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
                let args = self.conv_generic_args(env, def_id, args0)?;
                let refine_args = refine_args
                    .iter()
                    .map(|arg| self.conv_refine_arg(env, arg))
                    .collect_vec();
                let alias_ty = rty::AliasTy::new(def_id, args, refine_args);
                Ok(rty::Ty::alias(rty::AliasKind::Opaque, alias_ty))
            }
        }
    }

    fn conv_base_ty(&self, env: &mut Env, bty: &fhir::BaseTy) -> QueryResult<rty::Ty> {
        let sort = self.genv.sort_of_bty(bty);

        if let fhir::BaseTyKind::Path(fhir::QPath::Resolved(self_ty, path)) = &bty.kind {
            if let fhir::Res::Def(DefKind::AssocTy, def_id) = path.res {
                assert!(path.args.is_empty(), "generic associated types are not supported");
                let self_ty = self.conv_ty(env, self_ty.as_deref().unwrap())?;
                let args = List::singleton(rty::GenericArg::Ty(self_ty));
                let refine_args = List::empty();
                let alias_ty = rty::AliasTy { args, refine_args, def_id };
                return Ok(rty::Ty::alias(rty::AliasKind::Projection, alias_ty));
            }
            // If it is a type parameter with no sort, it means it is of kind `Type`
            if let fhir::Res::SelfTyParam { .. } = path.res
                && sort.is_none()
            {
                return Ok(rty::Ty::param(self_param_ty()));
            }
            if let fhir::Res::Def(DefKind::TyParam, def_id) = path.res
                && sort.is_none()
            {
                let param_ty = def_id_to_param_ty(self.genv.tcx, def_id.expect_local());
                return Ok(rty::Ty::param(param_ty));
            }
        }
        let sort = conv_sort(self.genv, &sort.unwrap());
        if sort.is_unit() {
            let idx = rty::Expr::unit();
            self.conv_indexed_type(env, bty, idx)
        } else if let Some(def_id) = sort.is_unit_adt() {
            let idx = rty::Expr::unit_adt(def_id);
            self.conv_indexed_type(env, bty, idx)
        } else {
            env.push_layer(Layer::empty());
            let idx = rty::Expr::nu();
            let ty = self.conv_indexed_type(env, bty, idx)?;
            env.pop_layer();
            Ok(rty::Ty::exists(rty::Binder::with_sort(ty, sort)))
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
        let tcx = self.genv.tcx;
        let lifetime_name = |def_id| tcx.hir().name(tcx.hir().local_def_id_to_hir_id(def_id));
        match res {
            ResolvedArg::StaticLifetime => rty::ReStatic,
            ResolvedArg::EarlyBound(def_id) => {
                let index = def_id_to_param_index(self.genv.tcx, def_id.expect_local());
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

    fn conv_refine_arg(&self, env: &mut Env, arg: &fhir::RefineArg) -> rty::Expr {
        match &arg.kind {
            fhir::RefineArgKind::Expr(expr) => self.conv_expr(env, expr),
            fhir::RefineArgKind::Abs(params, body) => {
                let layer = Layer::list(self, 0, params, false);

                env.push_layer(layer);
                let pred = self.conv_expr(env, body);
                let vars = env.pop_layer().into_bound_vars(self.genv);
                let body = rty::Binder::new(pred, vars);
                self.add_coercions(rty::Expr::abs(body), arg.fhir_id)
            }
            fhir::RefineArgKind::Record(flds) => {
                let (def_id, ..) = self.wfckresults.record_ctors().get(arg.fhir_id).unwrap();
                let flds: List<_> = flds
                    .iter()
                    .map(|arg| self.conv_refine_arg(env, arg))
                    .collect();
                rty::Expr::record(*def_id, flds)
            }
        }
    }

    fn conv_indexed_type(
        &self,
        env: &mut Env,
        bty: &fhir::BaseTy,
        idx: rty::Expr,
    ) -> QueryResult<rty::Ty> {
        match &bty.kind {
            fhir::BaseTyKind::Path(fhir::QPath::Resolved(_, path)) => {
                self.conv_indexed_path(env, path, idx)
            }
            fhir::BaseTyKind::Slice(ty) => {
                let slice = rty::BaseTy::slice(self.conv_ty(env, ty)?);
                Ok(rty::Ty::indexed(slice, idx))
            }
        }
    }

    fn conv_indexed_path(
        &self,
        env: &mut Env,
        path: &fhir::Path,
        idx: rty::Expr,
    ) -> QueryResult<rty::Ty> {
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
                let args = self.conv_generic_args(env, *did, &path.args)?;
                rty::BaseTy::adt(adt_def, args)
            }
            fhir::Res::Def(DefKind::TyParam, def_id) => {
                rty::BaseTy::Param(def_id_to_param_ty(self.genv.tcx, def_id.expect_local()))
            }
            fhir::Res::SelfTyParam { .. } => rty::BaseTy::Param(self_param_ty()),
            fhir::Res::SelfTyAlias { alias_to, .. } => {
                return Ok(self
                    .genv
                    .type_of(*alias_to)?
                    .instantiate_identity(&[])
                    .replace_bound_expr(&idx));
            }
            fhir::Res::Def(DefKind::TyAlias { .. }, def_id) => {
                let generics = self.conv_generic_args(env, *def_id, &path.args)?;
                let refine = path
                    .refine
                    .iter()
                    .map(|arg| self.conv_refine_arg(env, arg))
                    .collect_vec();
                return Ok(self
                    .genv
                    .type_of(*def_id)?
                    .instantiate(&generics, &refine)
                    .replace_bound_expr(&idx));
            }
            fhir::Res::Def(..) => {
                span_bug!(path.span, "unexpected resolution in conv_indexed_path: {:?}", path.res)
            }
        };
        Ok(rty::Ty::indexed(bty, idx))
    }

    fn conv_generic_args(
        &self,
        env: &mut Env,
        def_id: DefId,
        args: &[fhir::GenericArg],
    ) -> QueryResult<Vec<rty::GenericArg>> {
        let mut into = vec![];
        self.conv_generic_args_into(env, args, &mut into)?;
        self.fill_generic_args_defaults(def_id, &mut into)?;
        Ok(into)
    }

    fn conv_generic_args_into(
        &self,
        env: &mut Env,
        args: &[fhir::GenericArg],
        into: &mut Vec<rty::GenericArg>,
    ) -> QueryResult<()> {
        for arg in args {
            match arg {
                fhir::GenericArg::Lifetime(lft) => {
                    into.push(rty::GenericArg::Lifetime(self.conv_lifetime(env, *lft)));
                }
                fhir::GenericArg::Type(ty) => {
                    into.push(rty::GenericArg::Ty(self.conv_ty(env, ty)?));
                }
            }
        }
        Ok(())
    }

    fn fill_generic_args_defaults(
        &self,
        def_id: DefId,
        into: &mut Vec<rty::GenericArg>,
    ) -> QueryResult<()> {
        let generics = self.genv.generics_of(def_id)?;
        for param in generics.params.iter().skip(into.len()) {
            if let rty::GenericParamDefKind::Type { has_default } = param.kind {
                debug_assert!(has_default);
                let ty = self
                    .genv
                    .type_of(param.def_id)?
                    .instantiate(into, &[])
                    .into_ty();
                into.push(rty::GenericArg::Ty(ty));
            } else {
                bug!("unexpected generic param: {param:?}");
            }
        }

        Ok(())
    }

    fn resolve_param_sort(&self, param: &fhir::RefineParam) -> fhir::Sort {
        resolve_param_sort(param, self.wfckresults).clone()
    }
}

impl Env {
    fn new(early_bound: &[fhir::RefineParam], wfckresults: &fhir::WfckResults) -> Self {
        let early_bound = early_bound
            .iter()
            .map(|param| (param.name(), resolve_param_sort(param, wfckresults).clone()))
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

    fn lookup(&self, name: fhir::Ident) -> LookupResult {
        for (level, layer) in self.layers.iter().rev().enumerate() {
            if let Some(kind) = layer.get(name.name, level as u32) {
                return LookupResult { name, kind };
            }
        }
        if let Some((idx, _, sort)) = self.early_bound.get_full(&name.name) {
            LookupResult { name, kind: LookupResultKind::EarlyBound { idx: idx as u32, sort } }
        } else {
            span_bug!(name.span(), "no entry found for key: `{:?}`", name);
        }
    }

    fn to_early_bound_vars(&self) -> List<rty::Expr> {
        (0..self.early_bound.len())
            .map(|idx| rty::Expr::early_bvar(idx as u32))
            .collect()
    }
}

impl ConvCtxt<'_, '_> {
    fn conv_expr(&self, env: &Env, expr: &fhir::Expr) -> rty::Expr {
        let fhir_id = expr.fhir_id;
        let espan = Some(ESpan::new(expr.span));
        let expr = match &expr.kind {
            fhir::ExprKind::Const(did, _) => rty::Expr::const_def_id(*did, espan),
            fhir::ExprKind::Var(var, _) => env.lookup(*var).to_expr(),
            fhir::ExprKind::Literal(lit) => rty::Expr::constant_at(conv_lit(*lit), espan),
            fhir::ExprKind::BinaryOp(op, box [e1, e2]) => {
                rty::Expr::binary_op(*op, self.conv_expr(env, e1), self.conv_expr(env, e2), espan)
            }
            fhir::ExprKind::UnaryOp(op, e) => {
                rty::Expr::unary_op(*op, self.conv_expr(env, e), espan)
            }
            fhir::ExprKind::App(func, args) => {
                rty::Expr::app(self.conv_func(env, func), self.conv_exprs(env, args), espan)
            }
            fhir::ExprKind::IfThenElse(box [p, e1, e2]) => {
                rty::Expr::ite(
                    self.conv_expr(env, p),
                    self.conv_expr(env, e1),
                    self.conv_expr(env, e2),
                    espan,
                )
            }
            fhir::ExprKind::Dot(var, fld) => env.lookup(*var).get_field(self.genv, *fld),
        };
        self.add_coercions(expr, fhir_id)
    }

    fn conv_func(&self, env: &Env, func: &fhir::Func) -> rty::Expr {
        let expr = match func {
            fhir::Func::Var(ident, _) => env.lookup(*ident).to_expr(),
            fhir::Func::Global(sym, kind, ..) => rty::Expr::global_func(*sym, *kind),
        };
        self.add_coercions(expr, func.fhir_id())
    }

    fn conv_exprs(&self, env: &Env, exprs: &[fhir::Expr]) -> List<rty::Expr> {
        List::from_iter(exprs.iter().map(|e| self.conv_expr(env, e)))
    }

    fn conv_invariants(&self, env: &Env, invariants: &[fhir::Expr]) -> Vec<rty::Invariant> {
        invariants
            .iter()
            .map(|invariant| self.conv_invariant(env, invariant))
            .collect()
    }

    fn conv_invariant(&self, env: &Env, invariant: &fhir::Expr) -> rty::Invariant {
        rty::Invariant::new(rty::Binder::new(
            self.conv_expr(env, invariant),
            env.top_layer().to_bound_vars(self.genv),
        ))
    }

    fn add_coercions(&self, mut expr: rty::Expr, fhir_id: FhirId) -> rty::Expr {
        let span = expr.span();
        if let Some(coercions) = self.wfckresults.coercions().get(fhir_id) {
            for coercion in coercions {
                expr = match *coercion {
                    fhir::Coercion::Inject(def_id) => {
                        rty::Expr::record(def_id, List::singleton(expr))
                    }
                    fhir::Coercion::Project(def_id) => {
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
                let entry = Entry::new(cx.genv, idx, sort, param.infer_mode());
                if !filter_unit || !matches!(entry, Entry::Unit) {
                    idx += 1;
                }
                (param.name(), entry)
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

    fn empty() -> Self {
        Self { map: FxIndexMap::default(), filter_unit: false, kind: LayerKind::List }
    }

    fn get(&self, name: impl Borrow<fhir::Name>, level: u32) -> Option<LookupResultKind> {
        Some(LookupResultKind::LateBoundList {
            level,
            entry: self.map.get(name.borrow())?,
            kind: self.kind,
        })
    }

    fn into_bound_vars(self, genv: &GlobalEnv) -> List<rty::BoundVariableKind> {
        match self.kind {
            LayerKind::List => {
                self.into_iter()
                    .map(|(sort, mode)| rty::BoundVariableKind::Refine(sort, mode))
                    .collect()
            }
            LayerKind::Record(def_id) => {
                let sort_def = genv.adt_sort_def_of(def_id);
                let args = sort_def.identity_args();
                let sort = rty::Sort::Adt(sort_def, args);
                let infer_mode = sort.default_infer_mode();
                List::singleton(rty::BoundVariableKind::Refine(sort, infer_mode))
            }
        }
    }

    fn to_bound_vars(&self, genv: &GlobalEnv) -> List<rty::BoundVariableKind> {
        self.clone().into_bound_vars(genv)
    }

    fn into_iter(self) -> impl Iterator<Item = (rty::Sort, rty::InferMode)> {
        self.map.into_values().filter_map(move |entry| {
            match entry {
                Entry::Sort { infer_mode, conv, .. } => Some((conv, infer_mode)),
                Entry::Unit => {
                    if self.filter_unit {
                        None
                    } else {
                        let unit = rty::Sort::unit();
                        let infer_mode = unit.default_infer_mode();
                        Some((unit, infer_mode))
                    }
                }
            }
        })
    }
}

impl Entry {
    fn new(genv: &GlobalEnv, idx: u32, sort: fhir::Sort, infer_mode: fhir::InferMode) -> Self {
        let conv = conv_sort(genv, &sort);
        if conv.is_unit() {
            Entry::Unit
        } else {
            Entry::Sort { sort, infer_mode, conv, idx }
        }
    }
}

impl LookupResult<'_> {
    fn to_expr(&self) -> rty::Expr {
        match &self.kind {
            LookupResultKind::LateBoundList { level, entry: Entry::Sort { idx, .. }, kind } => {
                match *kind {
                    LayerKind::List => rty::Expr::late_bvar(DebruijnIndex::from_u32(*level), *idx),
                    LayerKind::Record(def_id) => {
                        rty::Expr::field_proj(
                            rty::Expr::late_bvar(DebruijnIndex::from_u32(*level), 0),
                            rty::FieldProj::Adt { def_id, field: *idx },
                            None,
                        )
                    }
                }
            }
            LookupResultKind::LateBoundList { entry: Entry::Unit, .. } => rty::Expr::unit(),
            LookupResultKind::EarlyBound { idx, .. } => rty::Expr::early_bvar(*idx),
        }
    }

    fn is_record(&self) -> Option<DefId> {
        match &self.kind {
            LookupResultKind::LateBoundList {
                entry: Entry::Sort { sort: fhir::Sort::Record(def_id, _), .. },
                ..
            } => Some(*def_id),
            LookupResultKind::EarlyBound { sort: fhir::Sort::Record(def_id, _), .. } => {
                Some(*def_id)
            }
            _ => None,
        }
    }

    fn to_path(&self) -> rty::Path {
        self.to_expr().to_path().unwrap_or_else(|| {
            span_bug!(self.name.span(), "expected path, found `{:?}`", self.to_expr())
        })
    }

    fn get_field(&self, genv: &GlobalEnv, fld: SurfaceIdent) -> rty::Expr {
        if let Some(def_id) = self.is_record() {
            let i = genv
                .field_index(def_id, fld.name)
                .unwrap_or_else(|| span_bug!(fld.span, "field `{fld:?}` not found in {def_id:?}"));
            rty::Expr::field_proj(
                self.to_expr(),
                rty::FieldProj::Adt { def_id, field: i as u32 },
                None,
            )
        } else {
            span_bug!(fld.span, "expected record sort")
        }
    }
}

pub fn conv_func_decl(genv: &GlobalEnv, uif: &fhir::FuncDecl) -> rty::FuncDecl {
    rty::FuncDecl { name: uif.name, sort: conv_func_sort(genv, &uif.sort), kind: uif.kind }
}

fn conv_sorts<'a>(
    genv: &GlobalEnv,
    sorts: impl IntoIterator<Item = &'a fhir::Sort>,
) -> Vec<rty::Sort> {
    sorts
        .into_iter()
        .map(|sort| conv_sort(genv, sort))
        .collect()
}

fn conv_refine_param(
    genv: &GlobalEnv,
    param: &fhir::RefineParam,
    wfckresults: &fhir::WfckResults,
) -> rty::RefineParam {
    let sort = conv_sort(genv, resolve_param_sort(param, wfckresults));
    let mode = param.infer_mode();
    rty::RefineParam { sort, mode }
}

fn resolve_param_sort<'a>(
    param: &'a fhir::RefineParam,
    wfckresults: &'a fhir::WfckResults,
) -> &'a fhir::Sort {
    if fhir::Sort::Wildcard == param.sort {
        wfckresults
            .node_sorts()
            .get(param.fhir_id)
            .unwrap_or_else(|| bug!("unresolved sort for param: `{param:?}`"))
    } else {
        &param.sort
    }
}

fn conv_sort(genv: &GlobalEnv, sort: &fhir::Sort) -> rty::Sort {
    match sort {
        fhir::Sort::Int => rty::Sort::Int,
        fhir::Sort::Real => rty::Sort::Real,
        fhir::Sort::Bool => rty::Sort::Bool,
        fhir::Sort::BitVec(w) => rty::Sort::BitVec(*w),
        fhir::Sort::Loc => rty::Sort::Loc,
        fhir::Sort::Unit => rty::Sort::unit(),
        fhir::Sort::Func(fsort) => rty::Sort::Func(conv_func_sort(genv, fsort)),
        fhir::Sort::Record(def_id, sort_args) => {
            rty::Sort::Adt(
                genv.adt_sort_def_of(*def_id),
                List::from_vec(conv_sorts(genv, sort_args)),
            )
        }
        fhir::Sort::App(ctor, args) => {
            let ctor = conv_sort_ctor(ctor);
            let args = args.iter().map(|t| conv_sort(genv, t)).collect_vec();
            rty::Sort::app(ctor, args)
        }
        fhir::Sort::Param(def_id) => {
            rty::Sort::Param(def_id_to_param_ty(genv.tcx, def_id.expect_local()))
        }
        fhir::Sort::SelfParam { trait_id: _def_id } => rty::Sort::Param(self_param_ty()),
        fhir::Sort::SelfAlias { alias_to } => {
            conv_sort(genv, &genv.sort_of_self_ty_alias(*alias_to).unwrap())
        }
        fhir::Sort::Var(n) => rty::Sort::Var(rty::SortVar::from(*n)),
        fhir::Sort::Error | fhir::Sort::Wildcard | fhir::Sort::Infer(_) => {
            bug!("unexpected sort `{sort:?}`")
        }
    }
}

fn conv_sort_ctor(ctor: &fhir::SortCtor) -> rty::SortCtor {
    match ctor {
        fhir::SortCtor::Set => rty::SortCtor::Set,
        fhir::SortCtor::Map => rty::SortCtor::Map,
        fhir::SortCtor::User { name } => rty::SortCtor::User { name: *name },
    }
}

fn conv_func_sort(genv: &GlobalEnv, sort: &fhir::PolyFuncSort) -> rty::PolyFuncSort {
    let fsort = sort.skip_binders();
    let fsort =
        rty::FuncSort::new(conv_sorts(genv, fsort.inputs()), conv_sort(genv, fsort.output()));
    rty::PolyFuncSort::new(sort.params, fsort)
}

fn conv_lit(lit: fhir::Lit) -> rty::Constant {
    match lit {
        fhir::Lit::Int(n) => rty::Constant::from(n),
        fhir::Lit::Real(r) => rty::Constant::Real(r),
        fhir::Lit::Bool(b) => rty::Constant::from(b),
    }
}

fn def_id_to_param_ty(tcx: TyCtxt, def_id: LocalDefId) -> rty::ParamTy {
    rty::ParamTy {
        index: def_id_to_param_index(tcx, def_id),
        name: tcx.hir().ty_param_name(def_id),
    }
}

fn self_param_ty() -> rty::ParamTy {
    rty::ParamTy { index: 0, name: kw::SelfUpper }
}

fn def_id_to_param_index(tcx: TyCtxt, def_id: LocalDefId) -> u32 {
    let item_def_id = tcx.hir().ty_param_owner(def_id);
    let generics = tcx.generics_of(item_def_id);
    generics.param_def_id_to_index[&def_id.to_def_id()]
}

mod errors {
    use flux_macros::Diagnostic;
    use flux_middle::fhir::SurfaceIdent;
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
}
