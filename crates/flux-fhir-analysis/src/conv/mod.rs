//! Conversion from types in [`fhir`] to types in [`rty`]
//!
//! Conversion assumes well-formedness and will panic if type are not well-formed. Among other things,
//! well-formedness implies:
//! 1. Names are bound correctly.
//! 2. Refinement parameters appear in allowed positions. This is particularly important for
//!    refinement predicates, aka abstract refinements, since the syntax in [`rty`] has
//!    syntactic restrictions on predicates.
//! 3. Refinements are well-sorted.

pub mod struct_compat;
use std::{borrow::Borrow, iter};

use flux_common::{bug, iter::IterExt, span_bug};
use flux_middle::{
    fhir::{self, ExprRes, FhirId, FluxOwnerId},
    global_env::GlobalEnv,
    queries::{QueryErr, QueryResult},
    query_bug,
    rty::{
        self,
        fold::TypeFoldable,
        refining::{self, Refiner},
        ESpan, List, RefineArgsExt, WfckResults, INNERMOST,
    },
    MaybeExternId,
};
use flux_rustc_bridge::{lowering::Lower, ToRustc};
use itertools::Itertools;
use rustc_data_structures::fx::FxIndexMap;
use rustc_errors::Diagnostic;
use rustc_hash::FxHashSet;
use rustc_hir::{def::DefKind, def_id::DefId, OwnerId, PrimTy, Safety};
use rustc_middle::{
    middle::resolve_bound_vars::ResolvedArg,
    ty::{self, AssocItem, AssocKind, BoundRegionKind::BrNamed, BoundVar, TyCtxt},
};
use rustc_span::{
    symbol::{kw, Ident},
    ErrorGuaranteed, Span, Symbol, DUMMY_SP,
};
use rustc_target::spec::abi;
use rustc_trait_selection::traits;
use rustc_type_ir::DebruijnIndex;

use crate::compare_impl_item::errors::InvalidAssocReft;

/// Wrapper over a type implementing [`ConvPhase`]. We have this to implement most functionality as
/// inherent methods instead of defining them as default implementation in the trait definition.
#[repr(transparent)]
pub struct ConvCtxt<P>(P);

pub(crate) struct AfterSortck<'a, 'genv, 'tcx> {
    genv: GlobalEnv<'genv, 'tcx>,
    wfckresults: &'a WfckResults,
    next_sort_index: u32,
    next_type_index: u32,
    next_region_index: u32,
    next_const_index: u32,
}

/// We do conversion twice: once before sort checking when we don't have elaborated information
/// and then again after sort checking after all information has been elaborated. This is the
/// interface to configure conversion for both *phases*.
pub trait ConvPhase<'genv, 'tcx>: Sized {
    /// Whether to expand type aliases or to generate a *weak* [`rty::AliasTy`].
    const EXPAND_TYPE_ALIASES: bool;

    /// Whether we have elaborated information or not (in the first phase we will not, but in the
    /// second we will).
    const HAS_ELABORATED_INFORMATION: bool;

    type Results: WfckResultsProvider;

    fn genv(&self) -> GlobalEnv<'genv, 'tcx>;

    fn owner(&self) -> FluxOwnerId;

    fn next_sort_vid(&mut self) -> rty::SortVid;

    fn next_type_vid(&mut self) -> rty::TyVid;

    fn next_region_vid(&mut self) -> rty::RegionVid;

    fn next_const_vid(&mut self) -> rty::ConstVid;

    fn results(&self) -> &Self::Results;

    /// Called after converting an indexed type `b[e]` with the `fhir_id` and sort of `b`. Used
    /// during the first phase to collect the sort of base types.
    fn insert_bty_sort(&mut self, fhir_id: FhirId, sort: rty::Sort);

    /// Called after converting an [`fhir::ExprKind::Alias`] with the sort of the resulting
    /// [`rty::AliasReft`]. Used during the first phase to collect the sorts of refinement aliases.
    fn insert_alias_reft_sort(&mut self, fhir_id: FhirId, fsort: rty::FuncSort);

    fn into_conv_ctxt(self) -> ConvCtxt<Self> {
        ConvCtxt(self)
    }

    fn as_conv_ctxt(&mut self) -> &mut ConvCtxt<Self> {
        // SAFETY: `ConvCtxt` is `repr(transparent)` and it doesn't have any safety invariants.
        unsafe { std::mem::transmute(self) }
    }
}

/// An interface to the information elaborated during sort checking. We mock these results in
/// the first conversion phase during sort checking.
pub trait WfckResultsProvider: Sized {
    fn bin_rel_sort(&self, fhir_id: FhirId) -> rty::Sort;

    fn coercions_for(&self, fhir_id: FhirId) -> &[rty::Coercion];

    fn field_proj(&self, fhir_id: FhirId) -> rty::FieldProj;

    fn lambda_output(&self, fhir_id: FhirId) -> rty::Sort;

    fn record_ctor(&self, fhir_id: FhirId) -> DefId;

    fn param_sort(&self, param: &fhir::RefineParam) -> rty::Sort;
}

impl<'genv, 'tcx> ConvPhase<'genv, 'tcx> for AfterSortck<'_, 'genv, 'tcx> {
    const EXPAND_TYPE_ALIASES: bool = true;
    const HAS_ELABORATED_INFORMATION: bool = true;

    type Results = WfckResults;

    fn genv(&self) -> GlobalEnv<'genv, 'tcx> {
        self.genv
    }

    fn owner(&self) -> FluxOwnerId {
        self.wfckresults.owner
    }

    fn next_sort_vid(&mut self) -> rty::SortVid {
        self.next_sort_index = self.next_sort_index.checked_add(1).unwrap();
        rty::SortVid::from_u32(self.next_sort_index - 1)
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

    fn results(&self) -> &Self::Results {
        self.wfckresults
    }

    fn insert_bty_sort(&mut self, _: FhirId, _: rty::Sort) {}

    fn insert_alias_reft_sort(&mut self, _: FhirId, _: rty::FuncSort) {}
}

impl WfckResultsProvider for WfckResults {
    fn bin_rel_sort(&self, fhir_id: FhirId) -> rty::Sort {
        self.bin_rel_sorts()
            .get(fhir_id)
            .cloned()
            .unwrap_or_else(|| bug!("binary relation without elaborated sort `{fhir_id:?}`"))
    }

    fn coercions_for(&self, fhir_id: FhirId) -> &[rty::Coercion] {
        self.coercions().get(fhir_id).map_or(&[][..], Vec::as_slice)
    }

    fn field_proj(&self, fhir_id: FhirId) -> rty::FieldProj {
        *self
            .field_projs()
            .get(fhir_id)
            .unwrap_or_else(|| bug!("field projection without elaboration `{fhir_id:?}`"))
    }

    fn lambda_output(&self, fhir_id: FhirId) -> rty::Sort {
        self.node_sorts()
            .get(fhir_id)
            .unwrap_or_else(|| bug!("lambda without elaborated sort for `{fhir_id:?}`"))
            .clone()
    }

    fn record_ctor(&self, fhir_id: FhirId) -> DefId {
        *self
            .record_ctors()
            .get(fhir_id)
            .unwrap_or_else(|| bug!("unelaborated record constructor `{fhir_id:?}`"))
    }

    fn param_sort(&self, param: &fhir::RefineParam) -> rty::Sort {
        self.node_sorts()
            .get(param.fhir_id)
            .unwrap_or_else(|| bug!("unresolved sort for param `{param:?}`"))
            .clone()
    }
}

#[derive(Debug)]
pub(crate) struct Env {
    layers: Vec<Layer>,
    early_params: FxIndexMap<fhir::ParamId, Symbol>,
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
    Bound {
        debruijn: DebruijnIndex,
        entry: &'a ParamEntry,
        kind: LayerKind,
        /// The index of the parameter in the layer.
        index: u32,
    },
    EarlyParam {
        name: Symbol,
        /// The index of the parameter.
        index: u32,
    },
}

pub(crate) fn conv_adt_sort_def(
    genv: GlobalEnv,
    def_id: MaybeExternId,
    refined_by: &fhir::RefinedBy,
) -> QueryResult<rty::AdtSortDef> {
    let wfckresults = &WfckResults::new(OwnerId { def_id: def_id.local_id() });
    let mut cx = AfterSortck::new(genv, wfckresults).into_conv_ctxt();
    let params = refined_by
        .sort_params
        .iter()
        .map(|def_id| def_id_to_param_ty(genv, *def_id))
        .collect();
    let fields = refined_by
        .fields
        .iter()
        .map(|(name, sort)| -> QueryResult<_> { Ok((*name, cx.conv_sort(sort)?)) })
        .try_collect_vec()?;
    Ok(rty::AdtSortDef::new(def_id.resolved_id(), params, fields))
}

pub(crate) fn conv_generics(
    genv: GlobalEnv,
    generics: &fhir::Generics,
    def_id: MaybeExternId,
    is_trait: bool,
) -> rty::Generics {
    let opt_self = is_trait.then(|| {
        let kind = rty::GenericParamDefKind::Base { has_default: false };
        rty::GenericParamDef { index: 0, name: kw::SelfUpper, def_id: def_id.resolved_id(), kind }
    });
    let rust_generics = genv.tcx().generics_of(def_id.resolved_id());
    let params = {
        opt_self
            .into_iter()
            .chain(rust_generics.own_params.iter().flat_map(|rust_param| {
                // We have to filter out late bound parameters
                let param = generics
                    .params
                    .iter()
                    .find(|param| param.def_id.resolved_id() == rust_param.def_id)?;
                Some(rty::GenericParamDef {
                    kind: conv_generic_param_kind(&param.kind),
                    def_id: param.def_id.resolved_id(),
                    index: rust_param.index,
                    name: rust_param.name,
                })
            }))
            .collect_vec()
    };

    let rust_generics = genv.tcx().generics_of(def_id.resolved_id());
    rty::Generics {
        own_params: List::from_vec(params),
        parent: rust_generics.parent,
        parent_count: rust_generics.parent_count,
        has_self: rust_generics.has_self,
    }
}

pub(crate) fn conv_refinement_generics(
    params: &[fhir::RefineParam],
    wfckresults: &WfckResults,
) -> QueryResult<List<rty::RefineParam>> {
    params
        .iter()
        .map(|param| {
            let sort = wfckresults.param_sort(param);
            let mode = rty::InferMode::from_param_kind(param.kind);
            Ok(rty::RefineParam { sort, name: param.name, mode })
        })
        .try_collect()
}

fn conv_generic_param_kind(kind: &fhir::GenericParamKind) -> rty::GenericParamDefKind {
    match kind {
        fhir::GenericParamKind::Type { default } => {
            rty::GenericParamDefKind::Base { has_default: default.is_some() }
        }
        fhir::GenericParamKind::Lifetime => rty::GenericParamDefKind::Lifetime,
        fhir::GenericParamKind::Const { .. } => {
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
    let mut cx = AfterSortck::new(genv, wfckresults).into_conv_ctxt();
    let mut env = Env::new(&[]);
    env.push_layer(Layer::coalesce(wfckresults, def_id.resolved_id(), params));
    cx.conv_invariants(&mut env, invariants)
}

pub(crate) fn conv_defn(
    genv: GlobalEnv,
    func: &fhir::SpecFunc,
    wfckresults: &WfckResults,
) -> QueryResult<Option<rty::SpecFunc>> {
    if let Some(body) = &func.body {
        let mut cx = AfterSortck::new(genv, wfckresults).into_conv_ctxt();
        let mut env = Env::new(&[]);
        env.push_layer(Layer::list(wfckresults, 0, func.args));
        let expr = cx.conv_expr(&mut env, body)?;
        let expr = rty::Binder::bind_with_vars(expr, env.pop_layer().into_bound_vars(genv)?);
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
    let mut cx = AfterSortck::new(genv, wfckresults).into_conv_ctxt();
    let mut env = Env::new(&[]);
    env.push_layer(Layer::list(wfckresults, 0, qualifier.args));
    let body = cx.conv_expr(&mut env, &qualifier.expr)?;
    let body = rty::Binder::bind_with_vars(body, env.pop_layer().into_bound_vars(genv)?);
    Ok(rty::Qualifier { name: qualifier.name, body, global: qualifier.global })
}

pub(crate) fn conv_default_type_parameter(
    genv: GlobalEnv,
    def_id: MaybeExternId,
    ty: &fhir::Ty,
    wfckresults: &WfckResults,
) -> QueryResult<rty::TyOrBase> {
    let mut env = Env::new(&[]);
    let idx = genv.def_id_to_param_index(def_id.resolved_id());
    let owner = ty_param_owner(genv, def_id.resolved_id());
    let param = genv.generics_of(owner)?.param_at(idx as usize, genv)?;
    let mut cx = AfterSortck::new(genv, wfckresults).into_conv_ctxt();
    let rty_ty = cx.conv_ty(&mut env, ty)?;
    cx.try_to_ty_or_base(param.kind, ty.span, &rty_ty)
}

impl<'a, 'genv, 'tcx> AfterSortck<'a, 'genv, 'tcx> {
    pub(crate) fn new(genv: GlobalEnv<'genv, 'tcx>, wfckresults: &'a WfckResults) -> Self {
        Self {
            genv,
            wfckresults,
            // We start sorts and types from 1 to skip the trait object dummy self type.
            // See [`rty::Ty::trait_object_dummy_self`]
            next_sort_index: 1,
            next_type_index: 1,
            next_region_index: 0,
            next_const_index: 0,
        }
    }
}

/// Delegate methods to P
impl<'genv, 'tcx: 'genv, P: ConvPhase<'genv, 'tcx>> ConvCtxt<P> {
    fn genv(&self) -> GlobalEnv<'genv, 'tcx> {
        self.0.genv()
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.0.genv().tcx()
    }

    fn owner(&self) -> FluxOwnerId {
        self.0.owner()
    }

    fn results(&self) -> &P::Results {
        self.0.results()
    }

    fn next_sort_vid(&mut self) -> rty::SortVid {
        self.0.next_sort_vid()
    }

    fn next_type_vid(&mut self) -> rty::TyVid {
        self.0.next_type_vid()
    }

    fn next_region_vid(&mut self) -> rty::RegionVid {
        self.0.next_region_vid()
    }

    fn next_const_vid(&mut self) -> rty::ConstVid {
        self.0.next_const_vid()
    }
}

/// Conversion of definitions
impl<'genv, 'tcx: 'genv, P: ConvPhase<'genv, 'tcx>> ConvCtxt<P> {
    pub(crate) fn conv_enum_variants(
        &mut self,
        enum_id: MaybeExternId,
        enum_def: &fhir::EnumDef,
    ) -> QueryResult<Vec<rty::PolyVariant>> {
        enum_def
            .variants
            .iter()
            .map(|variant| self.conv_enum_variant(enum_id, variant))
            .try_collect_vec()
    }

    fn conv_enum_variant(
        &mut self,
        enum_id: MaybeExternId,
        variant: &fhir::VariantDef,
    ) -> QueryResult<rty::PolyVariant> {
        let mut env = Env::new(&[]);
        env.push_layer(Layer::list(self.results(), 0, variant.params));

        let fields = variant
            .fields
            .iter()
            .map(|field| self.conv_ty(&mut env, &field.ty))
            .try_collect()?;

        let adt_def = self.genv().adt_def(enum_id)?;
        let idxs = self.conv_expr(&mut env, &variant.ret.idx)?;
        let variant = rty::VariantSig::new(
            adt_def,
            rty::GenericArg::identity_for_item(self.genv(), enum_id.resolved_id())?,
            fields,
            idxs,
        );

        Ok(rty::Binder::bind_with_vars(variant, env.pop_layer().into_bound_vars(self.genv())?))
    }

    pub(crate) fn conv_struct_variant(
        &mut self,
        struct_id: MaybeExternId,
        struct_def: &fhir::StructDef,
    ) -> QueryResult<rty::Opaqueness<rty::PolyVariant>> {
        let mut env = Env::new(&[]);
        env.push_layer(Layer::list(self.results(), 0, struct_def.params));

        if let fhir::StructKind::Transparent { fields } = &struct_def.kind {
            let adt_def = self.genv().adt_def(struct_id)?;

            let fields = fields
                .iter()
                .map(|field_def| self.conv_ty(&mut env, &field_def.ty))
                .try_collect()?;

            let vars = env.pop_layer().into_bound_vars(self.genv())?;
            let idx = rty::Expr::adt(
                struct_id.resolved_id(),
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
                rty::GenericArg::identity_for_item(self.genv(), struct_id.resolved_id())?,
                fields,
                idx,
            );
            let variant = rty::Binder::bind_with_vars(variant, vars);
            Ok(rty::Opaqueness::Transparent(variant))
        } else {
            Ok(rty::Opaqueness::Opaque)
        }
    }

    pub(crate) fn conv_type_alias(
        &mut self,
        ty_alias_id: MaybeExternId,
        ty_alias: &fhir::TyAlias,
    ) -> QueryResult<rty::TyCtor> {
        let generics = self
            .genv()
            .map()
            .get_generics(ty_alias_id.local_id())?
            .unwrap();

        let mut env = Env::new(generics.refinement_params);

        if let Some(index) = &ty_alias.index {
            env.push_layer(Layer::list(self.results(), 0, std::slice::from_ref(index)));
            let ty = self.conv_ty(&mut env, &ty_alias.ty)?;

            Ok(rty::Binder::bind_with_vars(ty, env.pop_layer().into_bound_vars(self.genv())?))
        } else {
            let ctor = self
                .conv_ty(&mut env, &ty_alias.ty)?
                .shallow_canonicalize()
                .as_ty_or_base()
                .as_base()
                .ok_or_else(|| self.emit(errors::InvalidBaseInstance::new(ty_alias.span)))?;
            Ok(ctor.to_ty_ctor())
        }
    }

    pub(crate) fn conv_constant_info(
        &mut self,
        def_id: MaybeExternId,
        constant_info: &fhir::ConstantInfo,
    ) -> QueryResult<rty::ConstantInfo> {
        todo!("CONV constant_info")
    }

    pub(crate) fn conv_fn_sig(
        &mut self,
        fn_id: MaybeExternId,
        fn_sig: &fhir::FnSig,
    ) -> QueryResult<rty::PolyFnSig> {
        let decl = &fn_sig.decl;
        let header = fn_sig.header;

        let late_bound_regions =
            refining::refine_bound_variables(&self.genv().lower_late_bound_vars(fn_id.local_id())?);

        let generics = self.genv().map().get_generics(fn_id.local_id())?.unwrap();
        let mut env = Env::new(generics.refinement_params);
        env.push_layer(Layer::list(self.results(), late_bound_regions.len() as u32, &[]));

        let fn_sig = self.conv_fn_decl(&mut env, header.safety, header.abi, decl)?;

        let vars = late_bound_regions
            .iter()
            .chain(env.pop_layer().into_bound_vars(self.genv())?.iter())
            .cloned()
            .collect();

        Ok(rty::PolyFnSig::bind_with_vars(fn_sig, vars))
    }

    pub(crate) fn conv_generic_predicates(
        &mut self,
        def_id: MaybeExternId,
        generics: &fhir::Generics,
    ) -> QueryResult<rty::EarlyBinder<rty::GenericPredicates>> {
        let env = &mut Env::new(generics.refinement_params);

        let mut clauses = vec![];
        for pred in generics.predicates {
            let span = pred.bounded_ty.span;
            let bounded_ty = self.conv_ty(env, &pred.bounded_ty)?;
            for clause in self.conv_generic_bounds(env, span, bounded_ty, pred.bounds)? {
                clauses.push(clause);
            }
        }
        let parent = self.tcx().predicates_of(def_id).parent;
        Ok(rty::EarlyBinder(rty::GenericPredicates { parent, predicates: List::from_vec(clauses) }))
    }

    pub(crate) fn conv_opaque_ty(
        &mut self,
        opaque_ty: &fhir::OpaqueTy,
    ) -> QueryResult<rty::Clauses> {
        let def_id = opaque_ty.def_id;
        let parent = self.tcx().local_parent(def_id.local_id());
        let refparams = &self
            .genv()
            .map()
            .get_generics(parent)?
            .unwrap()
            .refinement_params;

        let env = &mut Env::new(refparams);

        let args = rty::GenericArg::identity_for_item(self.genv(), def_id.resolved_id())?;
        let alias_ty = rty::AliasTy::new(def_id.resolved_id(), args, env.to_early_param_args());
        let self_ty = rty::BaseTy::opaque(alias_ty).to_ty();
        // FIXME(nilehmann) use a good span here
        Ok(self
            .conv_generic_bounds(env, DUMMY_SP, self_ty, opaque_ty.bounds)?
            .into_iter()
            .collect())
    }

    pub(crate) fn conv_assoc_reft_body(
        &mut self,
        params: &[fhir::RefineParam],
        body: &fhir::Expr,
        output: &fhir::Sort,
    ) -> QueryResult<rty::Lambda> {
        let mut env = Env::new(&[]);
        env.push_layer(Layer::list(self.results(), 0, params));
        let expr = self.conv_expr(&mut env, body)?;
        let inputs = env.pop_layer().into_bound_vars(self.genv())?;
        let output = self.conv_sort(output)?;
        Ok(rty::Lambda::bind_with_vars(expr, inputs, output))
    }
}

/// Conversion of sorts
impl<'genv, 'tcx: 'genv, P: ConvPhase<'genv, 'tcx>> ConvCtxt<P> {
    pub(crate) fn conv_sort(&mut self, sort: &fhir::Sort) -> QueryResult<rty::Sort> {
        let sort = match sort {
            fhir::Sort::Path(path) => self.conv_sort_path(path)?,
            fhir::Sort::BitVec(size) => rty::Sort::BitVec(rty::BvSize::Fixed(*size)),
            fhir::Sort::Loc => rty::Sort::Loc,
            fhir::Sort::Func(fsort) => rty::Sort::Func(self.conv_poly_func_sort(fsort)?),
            fhir::Sort::Infer => rty::Sort::Infer(rty::SortVar(self.next_sort_vid())),
        };
        Ok(sort)
    }

    fn conv_poly_func_sort(&mut self, sort: &fhir::PolyFuncSort) -> QueryResult<rty::PolyFuncSort> {
        let params = iter::repeat(rty::SortParamKind::Sort)
            .take(sort.params)
            .collect();
        Ok(rty::PolyFuncSort::new(params, self.conv_func_sort(&sort.fsort)?))
    }

    fn conv_func_sort(&mut self, fsort: &fhir::FuncSort) -> QueryResult<rty::FuncSort> {
        let inputs = fsort
            .inputs()
            .iter()
            .map(|sort| self.conv_sort(sort))
            .try_collect()?;
        Ok(rty::FuncSort::new(inputs, self.conv_sort(fsort.output())?))
    }

    fn conv_sort_path(&mut self, path: &fhir::SortPath) -> QueryResult<rty::Sort> {
        let ctor = match path.res {
            fhir::SortRes::PrimSort(fhir::PrimSort::Int) => {
                self.check_prim_sort_generics(path, fhir::PrimSort::Int)?;
                return Ok(rty::Sort::Int);
            }
            fhir::SortRes::PrimSort(fhir::PrimSort::Bool) => {
                self.check_prim_sort_generics(path, fhir::PrimSort::Bool)?;
                return Ok(rty::Sort::Bool);
            }
            fhir::SortRes::PrimSort(fhir::PrimSort::Real) => {
                self.check_prim_sort_generics(path, fhir::PrimSort::Real)?;
                return Ok(rty::Sort::Real);
            }
            fhir::SortRes::SortParam(n) => return Ok(rty::Sort::Var(rty::ParamSort::from(n))),
            fhir::SortRes::TyParam(def_id) => {
                if !path.args.is_empty() {
                    let err = errors::GenericsOnTyParam::new(
                        path.segments.last().unwrap().span,
                        path.args.len(),
                    );
                    Err(self.emit(err))?;
                }
                return Ok(rty::Sort::Param(def_id_to_param_ty(self.genv(), def_id)));
            }
            fhir::SortRes::SelfParam { .. } => {
                if !path.args.is_empty() {
                    let err = errors::GenericsOnSelf::new(
                        path.segments.last().unwrap().span,
                        path.args.len(),
                    );
                    Err(self.emit(err))?;
                }
                return Ok(rty::Sort::Param(rty::SELF_PARAM_TY));
            }
            fhir::SortRes::SelfAlias { alias_to } => {
                if !path.args.is_empty() {
                    let err = errors::GenericsOnSelf::new(
                        path.segments.last().unwrap().span,
                        path.args.len(),
                    );
                    Err(self.emit(err))?;
                }
                return Ok(self
                    .genv()
                    .sort_of_self_ty_alias(alias_to)?
                    .unwrap_or(rty::Sort::Err));
            }
            fhir::SortRes::SelfParamAssoc { trait_id, ident } => {
                let res = fhir::Res::SelfTyParam { trait_: trait_id };
                let assoc_segment =
                    fhir::PathSegment { args: &[], constraints: &[], ident, res: fhir::Res::Err };
                let mut env = Env::empty();
                let alias_ty =
                    self.conv_type_relative_path(&mut env, ident.span, res, &assoc_segment)?;
                return Ok(rty::Sort::Alias(rty::AliasKind::Projection, alias_ty));
            }
            fhir::SortRes::PrimSort(fhir::PrimSort::Set) => {
                self.check_prim_sort_generics(path, fhir::PrimSort::Set)?;
                rty::SortCtor::Set
            }
            fhir::SortRes::PrimSort(fhir::PrimSort::Map) => {
                self.check_prim_sort_generics(path, fhir::PrimSort::Map)?;
                rty::SortCtor::Map
            }
            fhir::SortRes::User { name } => {
                if !path.args.is_empty() {
                    let err = errors::GenericsOnUserDefinedOpaqueSort::new(
                        path.segments.last().unwrap().span,
                        path.args.len(),
                    );
                    Err(self.emit(err))?;
                }
                rty::SortCtor::User { name }
            }
            fhir::SortRes::Adt(def_id) => {
                let sort_def = self.genv().adt_sort_def_of(def_id)?;
                if path.args.len() > sort_def.param_count() {
                    let err = errors::IncorrectGenericsOnSort::new(
                        self.genv(),
                        def_id,
                        path.segments.last().unwrap().span,
                        path.args.len(),
                        sort_def.param_count(),
                    );
                    Err(self.emit(err))?;
                }
                rty::SortCtor::Adt(sort_def)
            }
        };
        let args = path.args.iter().map(|t| self.conv_sort(t)).try_collect()?;

        Ok(rty::Sort::app(ctor, args))
    }

    fn check_prim_sort_generics(
        &mut self,
        path: &fhir::SortPath<'_>,
        prim_sort: fhir::PrimSort,
    ) -> QueryResult {
        if path.args.len() != prim_sort.generics() {
            Err(emit_prim_sort_generics_error(self.genv(), path, prim_sort))?;
        }
        Ok(())
    }
}

/// Conversion of types
impl<'genv, 'tcx: 'genv, P: ConvPhase<'genv, 'tcx>> ConvCtxt<P> {
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
            env.push_layer(Layer::list(self.results(), 0, requires.params));
            let pred = self.conv_expr(env, &requires.pred)?;
            let sorts = env.pop_layer().into_bound_vars(self.genv())?;
            Ok(rty::Expr::forall(rty::Binder::bind_with_vars(pred, sorts)))
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

    fn conv_fn_output(
        &mut self,
        env: &mut Env,
        output: &fhir::FnOutput,
    ) -> QueryResult<rty::Binder<rty::FnOutput>> {
        env.push_layer(Layer::list(self.results(), 0, output.params));

        let ret = self.conv_ty(env, &output.ret)?;
        let ensures: List<rty::Ensures> = output
            .ensures
            .iter()
            .map(|ens| self.conv_ensures(env, ens))
            .try_collect()?;
        let output = rty::FnOutput::new(ret, ensures);

        let vars = env.pop_layer().into_bound_vars(self.genv())?;
        Ok(rty::Binder::bind_with_vars(output, vars))
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
                fhir::GenericBound::Trait(poly_trait_ref) => {
                    match poly_trait_ref.modifiers {
                        fhir::TraitBoundModifier::None => {
                            self.conv_poly_trait_ref(
                                env,
                                bounded_ty_span,
                                &bounded_ty,
                                poly_trait_ref,
                                &mut clauses,
                            )?;
                        }
                        fhir::TraitBoundModifier::Maybe => {
                            // Maybe bounds are only supported for `?Sized`. The effect of the maybe
                            // bound is to relax the default which is `Sized` to not have the `Sized`
                            // bound, so we just skip it here.
                        }
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
        let generic_params = &poly_trait_ref.bound_generic_params;
        let layer = Layer::list(self.results(), generic_params.len() as u32, &[]);
        env.push_layer(layer);

        let trait_id = poly_trait_ref.trait_def_id();
        let generics = self.genv().generics_of(trait_id)?;
        let trait_segment = poly_trait_ref.trait_ref.last_segment();

        let self_param = generics.param_at(0, self.genv())?;
        let mut args = vec![self
            .try_to_ty_or_base(self_param.kind, span, bounded_ty)?
            .into()];
        self.conv_generic_args_into(env, trait_id, trait_segment, &mut args)?;

        env.pop_layer();
        let vars = generic_params
            .iter()
            .map(|param| self.param_as_bound_var(param))
            .try_collect_vec()?;
        let poly_trait_ref = rty::Binder::bind_with_vars(
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
        let tcx = self.tcx();

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
        let span = term.span;
        let term = self.conv_ty(env, term)?;
        let term = self.ty_to_subset_ty_ctor(span, &term)?;

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

    fn trait_defines_associated_item_named(
        &self,
        trait_def_id: DefId,
        assoc_kind: AssocKind,
        assoc_name: Ident,
    ) -> Option<&'tcx AssocItem> {
        self.tcx()
            .associated_items(trait_def_id)
            .find_by_name_and_kind(self.tcx(), assoc_name, assoc_kind, trait_def_id)
    }

    fn conv_ty(&mut self, env: &mut Env, ty: &fhir::Ty) -> QueryResult<rty::Ty> {
        match &ty.kind {
            fhir::TyKind::BaseTy(bty) => Ok(self.conv_bty(env, bty)?.to_ty()),
            fhir::TyKind::Indexed(bty, idx) => {
                let fhir_id = bty.fhir_id;
                let rty::TyOrCtor::Ctor(ty_ctor) = self.conv_bty(env, bty)? else {
                    return Err(self.emit(errors::RefinedUnrefinableType::new(bty.span)))?;
                };
                let idx = self.conv_expr(env, idx)?;
                self.0.insert_bty_sort(fhir_id, ty_ctor.sort());
                Ok(ty_ctor.replace_bound_reft(&idx))
            }
            fhir::TyKind::Exists(params, ty) => {
                let layer = Layer::list(self.results(), 0, params);
                env.push_layer(layer);
                let ty = self.conv_ty(env, ty)?;
                let sorts = env.pop_layer().into_bound_vars(self.genv())?;
                if sorts.is_empty() {
                    Ok(ty.shift_out_escaping(1))
                } else {
                    Ok(rty::Ty::exists(rty::Binder::bind_with_vars(ty, sorts)))
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
                env.push_layer(Layer::list(
                    self.results(),
                    bare_fn.generic_params.len() as u32,
                    &[],
                ));
                let fn_sig =
                    self.conv_fn_decl(&mut env, bare_fn.safety, bare_fn.abi, bare_fn.decl)?;
                let vars = bare_fn
                    .generic_params
                    .iter()
                    .map(|param| self.param_as_bound_var(param))
                    .try_collect()?;
                let poly_fn_sig = rty::Binder::bind_with_vars(fn_sig, vars);
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
            fhir::TyKind::OpaqueDef(opaque_ty) => self.conv_opaque_def(env, opaque_ty),
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
    fn conv_opaque_def(
        &mut self,
        env: &mut Env,
        opaque_ty: &fhir::OpaqueTy,
    ) -> QueryResult<rty::Ty> {
        let def_id = opaque_ty.def_id;

        if P::HAS_ELABORATED_INFORMATION {
            let lifetimes = self.tcx().opaque_captured_lifetimes(def_id.local_id());

            let generics = self.tcx().generics_of(opaque_ty.def_id);

            let offset = generics.parent_count;

            let args = rty::GenericArg::for_item(self.genv(), def_id.resolved_id(), |param, _| {
                if let Some(i) = (param.index as usize).checked_sub(offset) {
                    let (lifetime, _) = lifetimes[i];
                    rty::GenericArg::Lifetime(self.conv_resolved_lifetime(env, lifetime))
                } else {
                    rty::GenericArg::from_param_def(param)
                }
            })?;
            let reft_args = rty::RefineArgs::identity_for_item(self.genv(), def_id.resolved_id())?;
            let alias_ty = rty::AliasTy::new(def_id.resolved_id(), args, reft_args);
            Ok(rty::BaseTy::opaque(alias_ty).to_ty())
        } else {
            // During sortck we need to run conv on the opaque type to collect sorts for base types
            // in the opaque type's bounds. After sortck, we don't need to because opaque types are
            // converted as part of `genv.item_bounds`.
            self.conv_opaque_ty(opaque_ty)?;

            // `RefineArgs::identity_for_item` uses `genv.refinement_generics_of` which in turn
            // requires `genv.check_wf`, so we simply return all empty here to avoid the circularity
            let alias_ty = rty::AliasTy::new(def_id.resolved_id(), List::empty(), List::empty());
            Ok(rty::BaseTy::opaque(alias_ty).to_ty())
        }
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
                    trait_bounds.push(rty::Binder::bind_with_vars(trait_pred.trait_ref, vars));
                }
                rty::ClauseKind::Projection(proj) => {
                    projection_bounds.push(rty::Binder::bind_with_vars(proj, vars));
                }
                rty::ClauseKind::TypeOutlives(_) => {}
                rty::ClauseKind::ConstArgHasType(..) => {
                    bug!("did not expect {pred:?} clause in object bounds");
                }
            }
        }

        // Separate between regular from auto traits
        let (mut auto_traits, regular_traits): (Vec<_>, Vec<_>) = trait_bounds
            .into_iter()
            .partition(|trait_ref| self.tcx().trait_is_auto(trait_ref.def_id()));

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
                    .stable_cmp(self.tcx(), b.as_ref().skip_binder())
            });
            List::from_vec(v)
        };

        let region = self.conv_lifetime(env, lifetime);
        Ok(rty::Ty::dynamic(existential_predicates, region))
    }

    pub(crate) fn conv_bty(
        &mut self,
        env: &mut Env,
        bty: &fhir::BaseTy,
    ) -> QueryResult<rty::TyOrCtor> {
        match &bty.kind {
            fhir::BaseTyKind::Path(fhir::QPath::Resolved(qself, path)) => {
                self.conv_qpath(env, *qself, path)
            }
            fhir::BaseTyKind::Path(fhir::QPath::TypeRelative(qself, segment)) => {
                let qself_res =
                    if let Some(path) = qself.as_path() { path.res } else { fhir::Res::Err };
                let alias_ty = self
                    .conv_type_relative_path(env, qself.span, qself_res, segment)?
                    .shift_in_escaping(1);
                let bty = rty::BaseTy::Alias(rty::AliasKind::Projection, alias_ty);
                let sort = bty.sort();
                let ty = rty::Ty::indexed(bty, rty::Expr::nu());
                Ok(rty::TyOrCtor::Ctor(rty::Binder::bind_with_sort(ty, sort)))
            }
            fhir::BaseTyKind::Slice(ty) => {
                let bty = rty::BaseTy::Slice(self.conv_ty(env, ty)?).shift_in_escaping(1);
                let sort = bty.sort();
                let ty = rty::Ty::indexed(bty, rty::Expr::nu());
                Ok(rty::TyOrCtor::Ctor(rty::Binder::bind_with_sort(ty, sort)))
            }
        }
    }

    fn conv_type_relative_path(
        &mut self,
        env: &mut Env,
        qself_span: Span,
        qself_res: fhir::Res,
        assoc_segment: &fhir::PathSegment,
    ) -> QueryResult<rty::AliasTy> {
        let tcx = self.tcx();
        let assoc_ident = assoc_segment.ident;

        let bound = match qself_res {
            fhir::Res::SelfTyAlias { alias_to: impl_def_id, is_trait_impl: true } => {
                let Some(trait_ref) = tcx.impl_trait_ref(impl_def_id) else {
                    // A cycle error occurred most likely (comment copied from rustc)
                    span_bug!(qself_span, "expected cycle error");
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
            fhir::Res::Def(DefKind::TyParam, param_id)
            | fhir::Res::SelfTyParam { trait_: param_id } => {
                let predicates = self.probe_type_param_bounds(param_id, assoc_ident);
                self.probe_single_bound_for_assoc_item(
                    || {
                        traits::transitive_bounds_that_define_assoc_item(
                            tcx,
                            predicates.iter_identity_copied().filter_map(|(p, _)| {
                                Some(p.as_trait_clause()?.map_bound(|t| t.trait_ref))
                            }),
                            assoc_ident,
                        )
                    },
                    assoc_ident,
                )?
            }
            _ => Err(self.emit(errors::AssocTypeNotFound::new(assoc_ident)))?,
        };

        let Some(trait_ref) = bound.no_bound_vars() else {
            // This is a programmer error and we should gracefully report it. It's triggered
            // by code like this
            // ```
            // trait Super<'a> { type Assoc; }
            // trait Child: for<'a> Super<'a> {}
            // fn foo<T: Child>(x: T::Assoc) {}
            // ```
            Err(self.emit(
                query_bug!("associated path with uninferred generic parameters")
                    .at(assoc_ident.span),
            ))?
        };

        let trait_ref = {
            let trait_ref = trait_ref
                .lower(tcx)
                .map_err(|err| QueryErr::unsupported(trait_ref.def_id, err.into_err()))?;
            self.refiner()?.refine_trait_ref(&trait_ref)?
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
        Ok(alias_ty)
    }

    /// Return the generics of the containing owner item
    fn refiner(&self) -> QueryResult<Refiner<'genv, 'tcx>> {
        match self.owner() {
            FluxOwnerId::Rust(owner_id) => {
                let def_id = self.genv().maybe_extern_id(owner_id.def_id);
                Refiner::default(self.genv(), def_id.resolved_id())
            }
            FluxOwnerId::Flux(_) => Err(query_bug!("cannot refine types insicde flux item")),
        }
    }

    fn probe_type_param_bounds(
        &self,
        param_id: DefId,
        assoc_ident: Ident,
    ) -> ty::EarlyBinder<'tcx, &'tcx [(ty::Clause<'tcx>, Span)]> {
        // We would like to do this computation on the resolved id for it to work with extern specs
        // but the `type_param_predicates` query is only defined for `LocalDefId`. This is mostly
        // fine because the worst that can happen is that we fail to infer a trait when using the
        // `T::Assoc` syntax and the user has to manually annotate it as `<T as Trait>::Assoc`
        // (or add it as a bound to the extern spec so it's returned by the query).
        let param_id = self
            .genv()
            .resolve_id(param_id)
            .as_maybe_extern()
            .unwrap()
            .local_id();
        match self.owner() {
            FluxOwnerId::Rust(owner_id) => {
                self.tcx()
                    .type_param_predicates((owner_id.def_id, param_id, assoc_ident))
            }
            FluxOwnerId::Flux(_) => ty::EarlyBinder::bind(&[]),
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
            return Err(self.emit(errors::AssocTypeNotFound::new(assoc_ident)));
        };

        if matching_candidates.next().is_some() {
            return Err(self.emit(errors::AmbiguousAssocType::new(assoc_ident)));
        }

        Ok(bound)
    }

    fn conv_lifetime(&mut self, env: &Env, lft: fhir::Lifetime) -> rty::Region {
        let res = match lft {
            fhir::Lifetime::Hole(_) => return rty::Region::ReVar(self.next_region_vid()),
            fhir::Lifetime::Resolved(res) => res,
        };
        self.conv_resolved_lifetime(env, res)
    }

    fn conv_resolved_lifetime(&mut self, env: &Env, res: ResolvedArg) -> rty::Region {
        let tcx = self.tcx();
        let lifetime_name = |def_id| tcx.item_name(def_id);
        match res {
            ResolvedArg::StaticLifetime => rty::ReStatic,
            ResolvedArg::EarlyBound(def_id) => {
                let index = self.genv().def_id_to_param_index(def_id.to_def_id());
                let name = lifetime_name(def_id.to_def_id());
                rty::ReEarlyParam(rty::EarlyParamRegion { index, name })
            }
            ResolvedArg::LateBound(_, index, def_id) => {
                let depth = env.depth().checked_sub(1).unwrap();
                let name = lifetime_name(def_id.to_def_id());
                let kind = rty::BoundRegionKind::BrNamed(def_id.to_def_id(), name);
                let var = BoundVar::from_u32(index);
                let bound_region = rty::BoundRegion { var, kind };
                rty::ReBound(rty::DebruijnIndex::from_usize(depth), bound_region)
            }
            ResolvedArg::Free(scope, id) => {
                let name = lifetime_name(id.to_def_id());
                let bound_region = rty::BoundRegionKind::BrNamed(id.to_def_id(), name);
                rty::ReLateParam(rty::LateParamRegion { scope: scope.to_def_id(), bound_region })
            }
            ResolvedArg::Error(_) => bug!("lifetime resolved to an error"),
        }
    }

    fn conv_const_arg(&mut self, cst: fhir::ConstArg) -> rty::Const {
        match cst.kind {
            fhir::ConstArgKind::Lit(lit) => rty::Const::from_usize(self.tcx(), lit),
            fhir::ConstArgKind::Param(def_id) => {
                rty::Const {
                    kind: rty::ConstKind::Param(def_id_to_param_const(self.genv(), def_id)),
                }
            }
            fhir::ConstArgKind::Infer => {
                rty::Const {
                    kind: rty::ConstKind::Infer(ty::InferConst::Var(self.next_const_vid())),
                }
            }
        }
    }

    fn conv_qpath(
        &mut self,
        env: &mut Env,
        qself: Option<&fhir::Ty>,
        path: &fhir::Path,
    ) -> QueryResult<rty::TyOrCtor> {
        let bty = match path.res {
            fhir::Res::PrimTy(PrimTy::Bool) => rty::BaseTy::Bool,
            fhir::Res::PrimTy(PrimTy::Str) => rty::BaseTy::Str,
            fhir::Res::PrimTy(PrimTy::Char) => rty::BaseTy::Char,
            fhir::Res::PrimTy(PrimTy::Int(int_ty)) => {
                rty::BaseTy::Int(rustc_middle::ty::int_ty(int_ty))
            }
            fhir::Res::PrimTy(PrimTy::Uint(uint_ty)) => {
                rty::BaseTy::Uint(rustc_middle::ty::uint_ty(uint_ty))
            }
            fhir::Res::PrimTy(PrimTy::Float(float_ty)) => {
                rty::BaseTy::Float(rustc_middle::ty::float_ty(float_ty))
            }
            fhir::Res::Def(DefKind::Struct | DefKind::Enum | DefKind::Union, did) => {
                let adt_def = self.genv().adt_def(did)?;
                let args = self.conv_generic_args(env, did, path.last_segment())?;
                rty::BaseTy::adt(adt_def, args)
            }
            fhir::Res::Def(DefKind::TyParam, def_id) => {
                let owner_id = ty_param_owner(self.genv(), def_id);
                let param_ty = def_id_to_param_ty(self.genv(), def_id);
                let param = self
                    .genv()
                    .generics_of(owner_id)?
                    .param_at(param_ty.index as usize, self.genv())?;
                match param.kind {
                    rty::GenericParamDefKind::Type { .. } => {
                        return Ok(rty::TyOrCtor::Ty(rty::Ty::param(param_ty)))
                    }
                    rty::GenericParamDefKind::Base { .. } => rty::BaseTy::Param(param_ty),
                    _ => return Err(query_bug!("unexpected param kind")),
                }
            }
            fhir::Res::SelfTyParam { trait_ } => {
                let param = &self.genv().generics_of(trait_)?.own_params[0];
                match param.kind {
                    rty::GenericParamDefKind::Type { .. } => {
                        return Ok(rty::TyOrCtor::Ty(rty::Ty::param(rty::SELF_PARAM_TY)))
                    }
                    rty::GenericParamDefKind::Base { .. } => rty::BaseTy::Param(rty::SELF_PARAM_TY),
                    _ => return Err(query_bug!("unexpected param kind")),
                }
            }
            fhir::Res::SelfTyAlias { alias_to, .. } => {
                if P::EXPAND_TYPE_ALIASES {
                    return Ok(self.genv().type_of(alias_to)?.instantiate_identity());
                } else {
                    rty::BaseTy::Alias(
                        rty::AliasKind::Weak,
                        rty::AliasTy {
                            def_id: alias_to,
                            args: List::empty(),
                            refine_args: List::empty(),
                        },
                    )
                }
            }
            fhir::Res::Def(DefKind::AssocTy, assoc_id) => {
                let trait_id = self.tcx().trait_of_item(assoc_id).unwrap();
                let [.., trait_segment, assoc_segment] = path.segments else {
                    span_bug!(path.span, "expected at least two segments");
                };

                let trait_generics = self.genv().generics_of(trait_id)?;
                let qself = self.conv_ty_to_generic_arg(
                    env,
                    &trait_generics.own_params[0],
                    qself.unwrap(),
                )?;
                let mut args = vec![qself];
                self.conv_generic_args_into(env, trait_id, trait_segment, &mut args)?;
                self.conv_generic_args_into(env, assoc_id, assoc_segment, &mut args)?;
                let args = List::from_vec(args);

                let refine_args = List::empty();
                let alias_ty = rty::AliasTy { args, refine_args, def_id: assoc_id };
                rty::BaseTy::Alias(rty::AliasKind::Projection, alias_ty)
            }
            fhir::Res::Def(DefKind::TyAlias, def_id) => {
                let args = self.conv_generic_args(env, def_id, path.last_segment())?;
                let refine_args = path
                    .refine
                    .iter()
                    .map(|expr| self.conv_expr(env, expr))
                    .try_collect_vec()?;
                if P::EXPAND_TYPE_ALIASES {
                    let tcx = self.tcx();
                    return Ok(self
                        .genv()
                        .type_of(def_id)?
                        .instantiate(tcx, &args, &refine_args));
                } else {
                    rty::BaseTy::Alias(
                        rty::AliasKind::Weak,
                        rty::AliasTy {
                            def_id,
                            args: List::from(args),
                            refine_args: List::from(refine_args),
                        },
                    )
                }
            }
            fhir::Res::Def(..) | fhir::Res::Err => {
                span_bug!(path.span, "unexpected resolution in conv_ty_ctor: {:?}", path.res)
            }
        };
        let sort = bty.sort();
        let bty = bty.shift_in_escaping(1);
        let ctor = rty::Binder::bind_with_sort(rty::Ty::indexed(bty, rty::Expr::nu()), sort);
        Ok(rty::TyOrCtor::Ctor(ctor))
    }

    fn param_as_bound_var(
        &mut self,
        param: &fhir::GenericParam,
    ) -> QueryResult<rty::BoundVariableKind> {
        let def_id = param.def_id.resolved_id();
        let name = self.tcx().item_name(def_id);
        match param.kind {
            fhir::GenericParamKind::Lifetime => {
                Ok(rty::BoundVariableKind::Region(BrNamed(def_id, name)))
            }
            fhir::GenericParamKind::Const { .. } | fhir::GenericParamKind::Type { .. } => {
                Err(query_bug!(def_id, "unsupported param kind `{:?}`", param.kind))
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
        let generics = self.genv().generics_of(def_id)?;

        self.check_generic_arg_count(&generics, def_id, segment)?;

        let len = into.len();
        for (idx, arg) in segment.args.iter().enumerate() {
            let param = generics.param_at(idx + len, self.genv())?;
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
        if let DefKind::Trait = self.genv().def_kind(def_id) {
            param_count -= 1;
        }

        let min = param_count - generics.own_default_count();
        let max = param_count;
        if min == max && found != min {
            Err(self.emit(errors::GenericArgCountMismatch::new(
                self.genv(),
                def_id,
                segment,
                min,
            )))?;
        }
        if found < min {
            Err(self.emit(errors::TooFewGenericArgs::new(self.genv(), def_id, segment, min)))?;
        }
        if found > max {
            Err(self.emit(errors::TooManyGenericArgs::new(self.genv(), def_id, segment, min)))?;
        }
        Ok(())
    }

    fn fill_generic_args_defaults(
        &mut self,
        def_id: DefId,
        into: &mut Vec<rty::GenericArg>,
    ) -> QueryResult {
        let generics = self.genv().generics_of(def_id)?;
        for param in generics.own_params.iter().skip(into.len()) {
            debug_assert!(matches!(
                param.kind,
                rty::GenericParamDefKind::Type { has_default: true }
                    | rty::GenericParamDefKind::Base { has_default: true }
            ));
            let span = self.tcx().def_span(param.def_id);
            // FIXME(nilehmann) we already know whether this is a type or a constructor so we could
            // directly check if the constructor returns a subset type.
            let ty = self
                .genv()
                .type_of(param.def_id)?
                .instantiate(self.tcx(), into, &[])
                .to_ty();
            into.push(self.try_to_ty_or_base(param.kind, span, &ty)?.into());
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
        Ok(self.try_to_ty_or_base(param.kind, ty.span, &rty_ty)?.into())
    }

    fn try_to_ty_or_base(
        &mut self,
        kind: rty::GenericParamDefKind,
        span: Span,
        ty: &rty::Ty,
    ) -> QueryResult<rty::TyOrBase> {
        match kind {
            rty::GenericParamDefKind::Type { .. } => Ok(rty::TyOrBase::Ty(ty.clone())),
            rty::GenericParamDefKind::Base { .. } => {
                Ok(rty::TyOrBase::Base(self.ty_to_subset_ty_ctor(span, ty)?))
            }
            _ => span_bug!(span, "unexpected param kind `{kind:?}`"),
        }
    }

    fn ty_to_subset_ty_ctor(&mut self, span: Span, ty: &rty::Ty) -> QueryResult<rty::SubsetTyCtor> {
        let ctor = if let rty::TyKind::Infer(vid) = ty.kind() {
            // do not generate sort holes for dummy self types
            let sort_vid =
                if vid.as_u32() == 0 { rty::SortVid::from_u32(0) } else { self.next_sort_vid() };
            rty::SubsetTyCtor::bind_with_sort(
                rty::SubsetTy::trivial(rty::BaseTy::Infer(*vid), rty::Expr::nu()),
                rty::Sort::Infer(rty::SortInfer::SortVar(sort_vid)),
            )
        } else {
            ty.shallow_canonicalize()
                .as_ty_or_base()
                .as_base()
                .ok_or_else(|| self.emit(errors::InvalidBaseInstance::new(span)))?
        };
        Ok(ctor)
    }

    #[track_caller]
    fn emit(&self, err: impl Diagnostic<'genv>) -> ErrorGuaranteed {
        self.genv().sess().emit_err(err)
    }
}

/// Conversion of expressions
impl<'genv, 'tcx: 'genv, P: ConvPhase<'genv, 'tcx>> ConvCtxt<P> {
    fn conv_expr(&mut self, env: &mut Env, expr: &fhir::Expr) -> QueryResult<rty::Expr> {
        let fhir_id = expr.fhir_id;
        let espan = ESpan::new(expr.span);
        let expr = match &expr.kind {
            fhir::ExprKind::Var(var, _) => {
                match var.res {
                    ExprRes::Param(..) => env.lookup(var).to_expr(),
                    ExprRes::Const(def_id) => rty::Expr::const_def_id(def_id).at(espan),
                    ExprRes::ConstGeneric(def_id) => {
                        rty::Expr::const_generic(def_id_to_param_const(self.genv(), def_id))
                            .at(espan)
                    }
                    ExprRes::NumConst(num) => {
                        rty::Expr::constant(rty::Constant::from(num)).at(espan)
                    }
                    ExprRes::GlobalFunc(..) => {
                        span_bug!(var.span, "unexpected func in var position")
                    }
                    ExprRes::Ctor(..) => {
                        span_bug!(var.span, "unexpected constructor in var position")
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
                let alias = self.conv_alias_reft(env, expr.fhir_id, alias)?;
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
            fhir::ExprKind::Dot(var, _) => {
                let proj = self.results().field_proj(fhir_id);
                rty::Expr::field_proj(env.lookup(var).to_expr(), proj)
            }
            fhir::ExprKind::Abs(params, body) => {
                let layer = Layer::list(self.results(), 0, params);
                env.push_layer(layer);
                let pred = self.conv_expr(env, body)?;
                let inputs = env.pop_layer().into_bound_vars(self.genv())?;
                let output = self.results().lambda_output(expr.fhir_id);
                let lam = rty::Lambda::bind_with_vars(pred, inputs, output);
                rty::Expr::abs(lam)
            }
            fhir::ExprKind::Record(flds) => {
                let def_id = self.results().record_ctor(expr.fhir_id);
                let flds = flds
                    .iter()
                    .map(|expr| self.conv_expr(env, expr))
                    .try_collect()?;
                rty::Expr::adt(def_id, flds)
            }
            fhir::ExprKind::Constructor(path, exprs, spread) => {
                let def_id = if let Some(path) = path {
                    match path.res {
                        ExprRes::Ctor(def_id) => def_id,
                        _ => span_bug!(path.span, "unexpected path in constructor"),
                    }
                } else {
                    self.results().record_ctor(expr.fhir_id)
                };
                let assns = self.conv_constructor_exprs(def_id, env, exprs, spread)?;
                rty::Expr::adt(def_id, assns)
            }
        };
        Ok(self.add_coercions(expr, fhir_id))
    }

    fn conv_constructor_exprs(
        &mut self,
        struct_def_id: DefId,
        env: &mut Env,
        exprs: &[fhir::FieldExpr],
        spread: &Option<&fhir::Spread>,
    ) -> QueryResult<List<rty::Expr>> {
        if !P::HAS_ELABORATED_INFORMATION {
            return Ok(List::default());
        };
        let struct_adt = self.genv().adt_sort_def_of(struct_def_id)?;
        let spread = spread
            .map(|spread| self.conv_expr(env, &spread.expr))
            .transpose()?;
        let field_exprs_by_name: FxIndexMap<Symbol, &fhir::FieldExpr> =
            exprs.iter().map(|e| (e.ident.name, e)).collect();
        let mut assns = Vec::new();
        for (idx, field_name) in struct_adt.field_names().iter().enumerate() {
            if let Some(field_expr) = field_exprs_by_name.get(field_name) {
                assns.push(self.conv_expr(env, &field_expr.expr)?);
            } else if let Some(spread) = &spread {
                let proj = rty::FieldProj::Adt { def_id: struct_def_id, field: idx as u32 };
                assns.push(rty::Expr::field_proj(spread, proj));
            }
        }
        Ok(List::from_vec(assns))
    }

    fn conv_exprs(&mut self, env: &mut Env, exprs: &[fhir::Expr]) -> QueryResult<List<rty::Expr>> {
        exprs.iter().map(|e| self.conv_expr(env, e)).collect()
    }

    fn conv_bin_op(&self, op: fhir::BinOp, fhir_id: FhirId) -> rty::BinOp {
        match op {
            fhir::BinOp::Iff => rty::BinOp::Iff,
            fhir::BinOp::Imp => rty::BinOp::Imp,
            fhir::BinOp::Or => rty::BinOp::Or,
            fhir::BinOp::And => rty::BinOp::And,
            fhir::BinOp::Eq => rty::BinOp::Eq,
            fhir::BinOp::Ne => rty::BinOp::Ne,
            fhir::BinOp::Gt => rty::BinOp::Gt(self.results().bin_rel_sort(fhir_id)),
            fhir::BinOp::Ge => rty::BinOp::Ge(self.results().bin_rel_sort(fhir_id)),
            fhir::BinOp::Lt => rty::BinOp::Lt(self.results().bin_rel_sort(fhir_id)),
            fhir::BinOp::Le => rty::BinOp::Le(self.results().bin_rel_sort(fhir_id)),
            fhir::BinOp::Add => rty::BinOp::Add,
            fhir::BinOp::Sub => rty::BinOp::Sub,
            fhir::BinOp::Mod => rty::BinOp::Mod,
            fhir::BinOp::Mul => rty::BinOp::Mul,
            fhir::BinOp::Div => rty::BinOp::Div,
        }
    }

    fn add_coercions(&self, mut expr: rty::Expr, fhir_id: FhirId) -> rty::Expr {
        let span = expr.span();
        for coercion in self.results().coercions_for(fhir_id) {
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
        expr
    }

    fn conv_func(&self, env: &Env, func: &fhir::PathExpr) -> rty::Expr {
        let expr = match func.res {
            ExprRes::Param(..) => env.lookup(func).to_expr(),
            ExprRes::GlobalFunc(kind, sym) => rty::Expr::global_func(sym, kind),
            _ => span_bug!(func.span, "unexpected path in function position"),
        };
        self.add_coercions(expr, func.fhir_id)
    }

    fn conv_alias_reft(
        &mut self,
        env: &mut Env,
        fhir_id: FhirId,
        alias: &fhir::AliasReft,
    ) -> QueryResult<rty::AliasReft> {
        let fhir::Res::Def(DefKind::Trait, trait_id) = alias.path.res else {
            span_bug!(alias.path.span, "expected trait")
        };
        let trait_segment = alias.path.last_segment();

        let generics = self.genv().generics_of(trait_id)?;
        let self_ty =
            self.conv_ty_to_generic_arg(env, &generics.param_at(0, self.genv())?, alias.qself)?;
        let mut generic_args = vec![self_ty];
        self.conv_generic_args_into(env, trait_id, trait_segment, &mut generic_args)?;

        let alias_reft =
            rty::AliasReft { trait_id, name: alias.name, args: List::from_vec(generic_args) };

        let Some(fsort) = alias_reft.fsort(self.genv())? else {
            return Err(self.emit(InvalidAssocReft::new(
                alias.path.span,
                alias_reft.name,
                format!("{:?}", alias.path),
            )))?;
        };
        self.0.insert_alias_reft_sort(fhir_id, fsort);
        Ok(alias_reft)
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
        Ok(rty::Invariant::new(rty::Binder::bind_with_vars(
            self.conv_expr(env, invariant)?,
            env.top_layer().to_bound_vars(self.genv())?,
        )))
    }
}

impl Env {
    fn new(early_params: &[fhir::RefineParam]) -> Self {
        let early_params = early_params
            .iter()
            .map(|param| (param.id, param.name))
            .collect();
        Self { layers: vec![], early_params }
    }

    pub(crate) fn empty() -> Self {
        Self { layers: vec![], early_params: Default::default() }
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
                let kind = LookupResultKind::Bound {
                    debruijn,
                    entry,
                    index: idx as u32,
                    kind: layer.kind,
                };
                return LookupResult { var_span: var.span, kind };
            }
        }
        if let Some((idx, _, name)) = self.early_params.get_full(&id) {
            LookupResult {
                var_span: var.span,
                kind: LookupResultKind::EarlyParam { index: idx as u32, name: *name },
            }
        } else {
            span_bug!(var.span, "no entry found for key: `{:?}`", id);
        }
    }

    fn to_early_param_args(&self) -> List<rty::Expr> {
        self.early_params
            .iter()
            .enumerate()
            .map(|(idx, (_, name))| rty::Expr::early_param(idx as u32, *name))
            .collect()
    }
}

impl Layer {
    fn new<R: WfckResultsProvider>(
        results: &R,
        params: &[fhir::RefineParam],
        kind: LayerKind,
    ) -> Self {
        let map = params
            .iter()
            .map(|param| {
                let sort = results.param_sort(param);
                let infer_mode = rty::InferMode::from_param_kind(param.kind);
                let entry = ParamEntry::new(sort, infer_mode, param.name);
                (param.id, entry)
            })
            .collect();
        Self { map, kind }
    }

    fn list<R: WfckResultsProvider>(
        results: &R,
        bound_regions: u32,
        params: &[fhir::RefineParam],
    ) -> Self {
        Self::new(results, params, LayerKind::List { bound_regions })
    }

    fn coalesce<R: WfckResultsProvider>(
        results: &R,
        def_id: DefId,
        params: &[fhir::RefineParam],
    ) -> Self {
        Self::new(results, params, LayerKind::Coalesce(def_id))
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
            LookupResultKind::Bound { debruijn, entry: ParamEntry { name, .. }, kind, index } => {
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

    fn to_path(&self) -> rty::Path {
        self.to_expr().to_path().unwrap_or_else(|| {
            span_bug!(self.var_span, "expected path, found `{:?}`", self.to_expr())
        })
    }
}

pub fn conv_func_decl(genv: GlobalEnv, func: &fhir::SpecFunc) -> QueryResult<rty::SpecFuncDecl> {
    let wfckresults = WfckResults::new(FluxOwnerId::Flux(func.name));
    let mut cx = AfterSortck::new(genv, &wfckresults).into_conv_ctxt();
    let inputs_and_output = func
        .args
        .iter()
        .map(|p| &p.sort)
        .chain(iter::once(&func.sort))
        .map(|sort| cx.conv_sort(sort))
        .try_collect()?;
    let params = iter::repeat(rty::SortParamKind::Sort)
        .take(func.params)
        .collect();
    let sort = rty::PolyFuncSort::new(params, rty::FuncSort { inputs_and_output });
    let kind = if func.body.is_some() { fhir::SpecFuncKind::Def } else { fhir::SpecFuncKind::Uif };
    Ok(rty::SpecFuncDecl { name: func.name, sort, kind })
}

fn emit_prim_sort_generics_error(
    genv: GlobalEnv,
    path: &fhir::SortPath,
    prim_sort: fhir::PrimSort,
) -> ErrorGuaranteed {
    let err = errors::GenericsOnPrimitiveSort::new(
        path.segments.last().unwrap().span,
        prim_sort.name_str(),
        path.args.len(),
        prim_sort.generics(),
    );
    genv.sess().emit_err(err)
}

fn conv_lit(lit: fhir::Lit) -> rty::Constant {
    match lit {
        fhir::Lit::Int(n) => rty::Constant::from(n),
        fhir::Lit::Real(r) => rty::Constant::Real(rty::Real(r)),
        fhir::Lit::Bool(b) => rty::Constant::from(b),
        fhir::Lit::Str(s) => rty::Constant::from(s),
        fhir::Lit::Char(c) => rty::Constant::from(c),
    }
}
fn conv_un_op(op: fhir::UnOp) -> rty::UnOp {
    match op {
        fhir::UnOp::Not => rty::UnOp::Not,
        fhir::UnOp::Neg => rty::UnOp::Neg,
    }
}

fn def_id_to_param_ty(genv: GlobalEnv, def_id: DefId) -> rty::ParamTy {
    rty::ParamTy { index: genv.def_id_to_param_index(def_id), name: ty_param_name(genv, def_id) }
}

fn def_id_to_param_const(genv: GlobalEnv, def_id: DefId) -> rty::ParamConst {
    rty::ParamConst { index: genv.def_id_to_param_index(def_id), name: ty_param_name(genv, def_id) }
}

fn ty_param_owner(genv: GlobalEnv, def_id: DefId) -> DefId {
    let def_kind = genv.def_kind(def_id);
    match def_kind {
        DefKind::Trait | DefKind::TraitAlias => def_id,
        DefKind::LifetimeParam | DefKind::TyParam | DefKind::ConstParam => {
            genv.tcx().parent(def_id)
        }
        _ => bug!("ty_param_owner: {:?} is a {:?} not a type parameter", def_id, def_kind),
    }
}

fn ty_param_name(genv: GlobalEnv, def_id: DefId) -> Symbol {
    let def_kind = genv.tcx().def_kind(def_id);
    match def_kind {
        DefKind::Trait | DefKind::TraitAlias => kw::SelfUpper,
        DefKind::LifetimeParam | DefKind::TyParam | DefKind::ConstParam => {
            genv.tcx().item_name(def_id)
        }
        _ => bug!("ty_param_name: {:?} is a {:?} not a type parameter", def_id, def_kind),
    }
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

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_refined_unrefinable_type, code = E0999)]
    pub(super) struct RefinedUnrefinableType {
        #[primary_span]
        span: Span,
    }

    impl RefinedUnrefinableType {
        pub(super) fn new(span: Span) -> Self {
            Self { span }
        }
    }

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_generics_on_primitive_sort, code = E0999)]
    pub(super) struct GenericsOnPrimitiveSort {
        #[primary_span]
        #[label]
        span: Span,
        name: &'static str,
        found: usize,
        expected: usize,
    }

    impl GenericsOnPrimitiveSort {
        pub(super) fn new(span: Span, name: &'static str, found: usize, expected: usize) -> Self {
            Self { span, found, expected, name }
        }
    }

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_incorrect_generics_on_sort, code = E0999)]
    pub(super) struct IncorrectGenericsOnSort {
        #[primary_span]
        #[label]
        span: Span,
        found: usize,
        expected: usize,
        def_descr: &'static str,
    }

    impl IncorrectGenericsOnSort {
        pub(super) fn new(
            genv: GlobalEnv,
            def_id: DefId,
            span: Span,
            found: usize,
            expected: usize,
        ) -> Self {
            Self { span, found, expected, def_descr: genv.tcx().def_descr(def_id) }
        }
    }

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_generics_on_type_parameter, code = E0999)]
    pub(super) struct GenericsOnTyParam {
        #[primary_span]
        #[label]
        span: Span,
        found: usize,
    }

    impl GenericsOnTyParam {
        pub(super) fn new(span: Span, found: usize) -> Self {
            Self { span, found }
        }
    }

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_generics_on_self_alias, code = E0999)]
    pub(super) struct GenericsOnSelf {
        #[primary_span]
        #[label]
        span: Span,
        found: usize,
    }

    impl GenericsOnSelf {
        pub(super) fn new(span: Span, found: usize) -> Self {
            Self { span, found }
        }
    }

    #[derive(Diagnostic)]
    #[diag(fhir_analysis_generics_on_opaque_sort, code = E0999)]
    pub(super) struct GenericsOnUserDefinedOpaqueSort {
        #[primary_span]
        #[label]
        span: Span,
        found: usize,
    }

    impl GenericsOnUserDefinedOpaqueSort {
        pub(super) fn new(span: Span, found: usize) -> Self {
            Self { span, found }
        }
    }
}
