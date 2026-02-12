//! Checks type well-formedness
//!
//! Well-formedness checking assumes names are correctly bound which is guaranteed after desugaring.

mod errors;
mod param_usage;
mod sortck;

use flux_common::result::{ErrorCollector, ResultExt as _};
use flux_errors::Errors;
use flux_middle::{
    def_id::MaybeExternId,
    fhir::{self, FhirId, FluxOwnerId, visit::Visitor},
    global_env::GlobalEnv,
    queries::QueryResult,
    rty::{self, WfckResults},
};
use rustc_errors::ErrorGuaranteed;
use rustc_hash::FxHashSet;
use rustc_hir::{
    OwnerId,
    def::DefKind,
    def_id::{CrateNum, DefId, DefIndex},
};

use self::sortck::{ImplicitParamInferer, InferCtxt};
use crate::{
    conv::{ConvPhase, WfckResultsProvider},
    wf::sortck::prim_op_sort,
};

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

pub(crate) fn check_flux_item<'genv>(
    genv: GlobalEnv<'genv, '_>,
    item: fhir::FluxItem<'genv>,
) -> Result<WfckResults> {
    let owner = FluxOwnerId::Flux(item.def_id());
    let mut infcx = InferCtxt::new(genv, owner);

    Wf::with(&mut infcx, |wf| {
        wf.init_infcx_for_flux_item(item).emit(&genv)?;
        wf.check_flux_item(item);
        Ok(())
    })?;
    infcx.into_results()
}

pub(crate) fn check_constant_expr<'genv>(
    genv: GlobalEnv<'genv, '_>,
    owner: OwnerId,
    expr: &fhir::Expr<'genv>,
    sort: &rty::Sort,
) -> Result<WfckResults> {
    let mut infcx = InferCtxt::new(genv, FluxOwnerId::Rust(owner));
    Wf::with(&mut infcx, |wf| {
        wf.declare_params_in_expr(expr)?;
        wf.as_conv_ctxt()
            .conv_constant_expr(expr)
            .emit(&wf.errors)?;
        wf.check_expr(expr, sort);
        Ok(())
    })?;
    infcx.into_results()
}

pub(crate) fn check_invariants<'genv>(
    genv: GlobalEnv<'genv, '_>,
    adt_def_id: MaybeExternId<OwnerId>,
    params: &[fhir::RefineParam<'genv>],
    invariants: &[fhir::Expr<'genv>],
) -> Result<WfckResults> {
    let owner = FluxOwnerId::Rust(adt_def_id.local_id());
    let mut infcx = InferCtxt::new(genv, owner);
    Wf::with(&mut infcx, |wf| {
        wf.declare_params_for_invariants(params, invariants)?;

        // Run first conv phase to gather sorts for associated refinements.
        // This must run after declaring parameters because conversion expects
        // the parameter sorts to be present in wfckresults.
        wf.as_conv_ctxt()
            .conv_invariants(adt_def_id.map(|it| it.def_id), params, invariants)
            .emit(&wf.errors)?;

        for invariant in invariants {
            wf.check_expr(invariant, &rty::Sort::Bool);
        }
        Ok(())
    })?;
    infcx.into_results()
}

pub(crate) fn check_node<'genv>(
    genv: GlobalEnv<'genv, '_>,
    node: &fhir::OwnerNode<'genv>,
) -> Result<WfckResults> {
    let mut infcx = InferCtxt::new(genv, node.owner_id().local_id().into());
    Wf::with(&mut infcx, |wf| {
        wf.init_infcx_for_node(node)
            .map_err(|err| err.at(genv.tcx().def_span(node.owner_id().local_id())))
            .emit(&genv)?;

        ImplicitParamInferer::infer(wf.infcx, node)?;

        wf.check_node(node);
        Ok(())
    })?;

    param_usage::check(&infcx, node)?;

    infcx.into_results()
}

struct Wf<'a, 'genv, 'tcx> {
    infcx: &'a mut InferCtxt<'genv, 'tcx>,
    errors: Errors<'genv>,
    next_type_index: u32,
    next_region_index: u32,
    next_const_index: u32,
}

impl<'a, 'genv, 'tcx> Wf<'a, 'genv, 'tcx> {
    fn with(infcx: &'a mut InferCtxt<'genv, 'tcx>, f: impl FnOnce(&mut Self) -> Result) -> Result {
        let errors = Errors::new(infcx.genv.sess());
        let mut wf = Self {
            infcx,
            errors,
            // We start sorts and types from 1 to skip the trait object dummy self type.
            // See [`rty::Ty::trait_object_dummy_self`]
            next_type_index: 1,
            next_region_index: 0,
            next_const_index: 0,
        };
        f(&mut wf)?;
        wf.errors.into_result()
    }

    fn check_flux_item(&mut self, item: fhir::FluxItem<'genv>) {
        self.visit_flux_item(&item);
    }

    fn check_node(&mut self, node: &fhir::OwnerNode<'genv>) {
        self.visit_node(node);
    }

    fn check_expr(&mut self, expr: &fhir::Expr<'genv>, sort: &rty::Sort) {
        self.infcx
            .check_expr(expr, sort)
            .collect_err(&mut self.errors);
    }

    // We special-case primop applications to declare their parameters because their
    // parameters are implicit from the underlying primop and must not be declared explicitly.
    fn declare_params_for_primop_prop(&mut self, primop_prop: &fhir::PrimOpProp<'genv>) -> Result {
        let Some((sorts, _)) = prim_op_sort(&primop_prop.op) else {
            return Err(self
                .errors
                .emit(errors::UnsupportedPrimOp::new(primop_prop.span, primop_prop.op)));
        };
        if primop_prop.args.len() != sorts.len() {
            return Err(self.errors.emit(errors::ArgCountMismatch::new(
                Some(primop_prop.span),
                String::from("primop"),
                sorts.len(),
                primop_prop.args.len(),
            )));
        }
        for (arg, sort) in primop_prop.args.iter().zip(sorts) {
            self.infcx.declare_param(*arg, sort);
        }
        visit_refine_params(
            |vis| vis.visit_expr(&primop_prop.body),
            |param| self.declare_param(param),
        )
    }

    /// Recursively traverse `item` and declare all refinement parameters
    fn declare_params_for_flux_item(&mut self, item: fhir::FluxItem<'genv>) -> Result {
        if let fhir::FluxItem::PrimOpProp(primop_prop) = item {
            self.declare_params_for_primop_prop(primop_prop)
        } else {
            visit_refine_params(|vis| vis.visit_flux_item(&item), |param| self.declare_param(param))
        }
    }

    /// Recursively traverse `node` and declare all refinement parameters
    fn declare_params_for_node(&mut self, node: &fhir::OwnerNode<'genv>) -> Result {
        visit_refine_params(|vis| vis.visit_node(node), |param| self.declare_param(param))
    }

    /// Recursively traverse `invariants` and declare all refinement parameters
    fn declare_params_for_invariants(
        &mut self,
        params: &[fhir::RefineParam<'genv>],
        invariants: &[fhir::Expr<'genv>],
    ) -> Result {
        for param in params {
            self.declare_param(param)?;
        }
        for expr in invariants {
            self.declare_params_in_expr(expr)?;
        }
        Ok(())
    }

    fn declare_params_in_expr(&mut self, expr: &fhir::Expr<'genv>) -> Result {
        visit_refine_params(|vis| vis.visit_expr(expr), |param| self.declare_param(param))
    }

    fn declare_param(&mut self, param: &fhir::RefineParam<'genv>) -> Result {
        let sort = self
            .as_conv_ctxt()
            .conv_sort(&param.sort)
            .emit(&self.genv())?;
        self.infcx.declare_param(*param, sort);
        Ok(())
    }

    /// To check for well-formedness we need to synthesize sorts for some nodes which is hard to
    /// compute in `fhir`. For example, to check if the type `i32[e]` is well formed, we need to
    /// know that the sort of `i32` is `int` so we can check the expression `e` against it. Computing
    /// the sort from a base type is subtle and hard to do in `fhir` so we must do it in `rty`.
    /// However, to convert from `fhir` to `rty` we need elaborated information from sort checking
    /// which we do in `fhir`.
    ///
    /// To break this circularity, we do conversion in two phases. In the first phase, we do conversion
    /// without elaborated information. This results in types in `rty` with incorrect refinements but
    /// with the right *shape* to compute their sorts. We use these sorts for sort checking and then do
    /// conversion again with the elaborated information.
    ///
    /// This function initializes the [inference context] by running the first phase of conversion and
    /// collecting the sorts of some nodes that are hard to compute in `fhir`.
    ///
    /// [inference context]: InferCtxt
    fn init_infcx_for_node(&mut self, node: &fhir::OwnerNode<'genv>) -> QueryResult {
        let def_id = node.owner_id().map(|id| id.def_id);
        self.declare_params_for_node(node)?;
        let cx = self.as_conv_ctxt();
        match node {
            fhir::OwnerNode::Item(item) => {
                match &item.kind {
                    fhir::ItemKind::Enum(enum_def) => {
                        cx.conv_enum_variants(def_id, enum_def)?;
                        cx.conv_generic_predicates(def_id, &item.generics)?;
                    }
                    fhir::ItemKind::Struct(struct_def) => {
                        cx.conv_struct_variant(def_id, struct_def)?;
                        cx.conv_generic_predicates(def_id, &item.generics)?;
                    }
                    fhir::ItemKind::TyAlias(ty_alias) => {
                        cx.conv_type_alias(def_id, ty_alias)?;
                        cx.conv_generic_predicates(def_id, &item.generics)?;
                    }
                    fhir::ItemKind::Trait(trait_) => {
                        for assoc_reft in trait_.assoc_refinements {
                            if let Some(body) = assoc_reft.body {
                                cx.conv_assoc_reft_body(
                                    assoc_reft.params,
                                    &body,
                                    &assoc_reft.output,
                                )?;
                            }
                        }
                        cx.conv_generic_predicates(def_id, &item.generics)?;
                    }
                    fhir::ItemKind::Impl(impl_) => {
                        for assoc_reft in impl_.assoc_refinements {
                            cx.conv_assoc_reft_body(
                                assoc_reft.params,
                                &assoc_reft.body,
                                &assoc_reft.output,
                            )?;
                        }
                        cx.conv_generic_predicates(def_id, &item.generics)?;
                    }
                    fhir::ItemKind::Fn(fn_sig) => {
                        cx.conv_fn_sig(def_id, fn_sig)?;
                        cx.conv_generic_predicates(def_id, &item.generics)?;
                    }
                    fhir::ItemKind::Const(_) => {}
                }
            }
            fhir::OwnerNode::TraitItem(trait_item) => {
                match trait_item.kind {
                    fhir::TraitItemKind::Fn(fn_sig) => {
                        cx.conv_fn_sig(def_id, &fn_sig)?;
                        cx.conv_generic_predicates(def_id, &trait_item.generics)?;
                    }
                    fhir::TraitItemKind::Type => {}
                    fhir::TraitItemKind::Const => {}
                }
            }
            fhir::OwnerNode::ImplItem(impl_item) => {
                match impl_item.kind {
                    fhir::ImplItemKind::Fn(fn_sig) => {
                        cx.conv_fn_sig(def_id, &fn_sig)?;
                        cx.conv_generic_predicates(def_id, &impl_item.generics)?;
                    }
                    fhir::ImplItemKind::Type => {}
                    fhir::ImplItemKind::Const => {}
                }
            }
            fhir::OwnerNode::ForeignItem(impl_item) => {
                match impl_item.kind {
                    fhir::ForeignItemKind::Fn(fn_sig, generics) => {
                        cx.conv_fn_sig(def_id, &fn_sig)?;
                        cx.conv_generic_predicates(def_id, generics)?;
                    }
                }
            }
        }
        self.infcx.normalize_sorts()
    }

    fn init_infcx_for_flux_item(&mut self, item: fhir::FluxItem<'genv>) -> QueryResult {
        self.declare_params_for_flux_item(item)?;
        let cx = self.as_conv_ctxt();
        match item {
            fhir::FluxItem::Qualifier(qualifier) => {
                cx.conv_qualifier(qualifier)?;
            }
            fhir::FluxItem::Func(spec_func) => {
                cx.conv_defn(spec_func)?;
            }
            fhir::FluxItem::PrimOpProp(prim_op_prop) => {
                cx.conv_primop_prop(prim_op_prop)?;
            }
            fhir::FluxItem::SortDecl(_sort_decl) => {}
        }
        Ok(())
    }

    fn check_output_locs(&mut self, fn_decl: &fhir::FnDecl) {
        let mut output_locs = FxHashSet::default();
        for ens in fn_decl.output.ensures {
            if let fhir::Ensures::Type(loc, ..) = ens
                && let (_, id) = loc.res.expect_param()
                && !output_locs.insert(id)
            {
                self.errors.emit(errors::DuplicatedEnsures::new(loc));
            }
        }

        for ty in fn_decl.inputs {
            if let fhir::TyKind::StrgRef(_, loc, _) = ty.kind
                && let (_, id) = loc.res.expect_param()
                && !output_locs.contains(&id)
            {
                self.errors.emit(errors::MissingEnsures::new(loc));
            }
        }
    }
}

impl<'genv> fhir::visit::Visitor<'genv> for Wf<'_, 'genv, '_> {
    fn visit_qualifier(&mut self, qual: &fhir::Qualifier<'genv>) {
        self.check_expr(&qual.expr, &rty::Sort::Bool);
    }

    fn visit_primop_prop(&mut self, primop_prop: &fhir::PrimOpProp<'genv>) {
        let Some((sorts, _)) = prim_op_sort(&primop_prop.op) else {
            self.errors
                .emit(errors::UnsupportedPrimOp::new(primop_prop.span, primop_prop.op));
            return;
        };

        if primop_prop.args.len() != sorts.len() {
            self.errors.emit(errors::ArgCountMismatch::new(
                Some(primop_prop.span),
                String::from("primop"),
                sorts.len(),
                primop_prop.args.len(),
            ));
            return;
        }
        self.check_expr(&primop_prop.body, &rty::Sort::Bool);
    }

    fn visit_func(&mut self, func: &fhir::SpecFunc<'genv>) {
        if let Some(body) = &func.body {
            let Ok(output) = self.as_conv_ctxt().conv_sort(&func.sort).emit(&self.errors) else {
                return;
            };
            self.check_expr(body, &output);
        }
    }

    fn visit_impl_assoc_reft(&mut self, assoc_reft: &fhir::ImplAssocReft<'genv>) {
        let Ok(output) = self
            .as_conv_ctxt()
            .conv_sort(&assoc_reft.output)
            .emit(&self.errors)
        else {
            return;
        };
        self.check_expr(&assoc_reft.body, &output);
    }

    fn visit_trait_assoc_reft(&mut self, assoc_reft: &fhir::TraitAssocReft<'genv>) {
        if let Some(body) = &assoc_reft.body {
            let Ok(output) = self
                .as_conv_ctxt()
                .conv_sort(&assoc_reft.output)
                .emit(&self.errors)
            else {
                return;
            };
            self.check_expr(body, &output);
        }
    }

    fn visit_variant_ret(&mut self, ret: &fhir::VariantRet<'genv>) {
        let genv = self.infcx.genv;
        let enum_id = ret.enum_id;
        let Ok(adt_sort_def) = genv.adt_sort_def_of(enum_id).emit(&self.errors) else { return };
        if adt_sort_def.is_reflected() {
            return;
        }
        let Ok(args) = rty::GenericArg::identity_for_item(genv, enum_id).emit(&self.errors) else {
            return;
        };
        let expected = adt_sort_def.to_sort(&args);
        self.check_expr(&ret.idx, &expected);
    }

    fn visit_fn_decl(&mut self, decl: &fhir::FnDecl<'genv>) {
        fhir::visit::walk_fn_decl(self, decl);
        self.check_output_locs(decl);
    }

    fn visit_requires(&mut self, requires: &fhir::Requires<'genv>) {
        self.check_expr(&requires.pred, &rty::Sort::Bool);
    }

    fn visit_ensures(&mut self, ensures: &fhir::Ensures<'genv>) {
        match ensures {
            fhir::Ensures::Type(loc, ty) => {
                self.infcx.check_loc(loc).collect_err(&mut self.errors);
                self.visit_ty(ty);
            }
            fhir::Ensures::Pred(pred) => {
                self.check_expr(pred, &rty::Sort::Bool);
            }
        }
    }

    fn visit_ty(&mut self, ty: &fhir::Ty<'genv>) {
        match &ty.kind {
            fhir::TyKind::Indexed(bty, idx) => {
                let expected = self.infcx.sort_of_bty(bty);
                self.check_expr(idx, &expected);
                self.visit_bty(bty);
            }
            fhir::TyKind::StrgRef(_, loc, ty) => {
                self.infcx.check_loc(loc).collect_err(&mut self.errors);
                self.visit_ty(ty);
            }
            fhir::TyKind::Constr(pred, ty) => {
                self.visit_ty(ty);
                self.check_expr(pred, &rty::Sort::Bool);
            }
            _ => fhir::visit::walk_ty(self, ty),
        }
    }

    fn visit_path(&mut self, path: &fhir::Path<'genv>) {
        let genv = self.genv();
        if let fhir::Res::Def(DefKind::TyAlias, def_id) = path.res {
            let Ok(generics) = genv.refinement_generics_of(def_id).emit(&self.errors) else {
                return;
            };

            let args = self.infcx.path_args(path.fhir_id);
            for (i, expr) in path.refine.iter().enumerate() {
                let Ok(param) = generics.param_at(i, genv).emit(&self.errors) else { return };
                let param = param.instantiate(genv.tcx(), &args, &[]);
                self.check_expr(expr, &param.sort);
            }
        };
        fhir::visit::walk_path(self, path);
    }
}

struct RefineParamVisitor<F> {
    f: F,
    err: Option<ErrorGuaranteed>,
}

impl<'v, F> fhir::visit::Visitor<'v> for RefineParamVisitor<F>
where
    F: FnMut(&fhir::RefineParam<'v>) -> Result,
{
    fn visit_refine_param(&mut self, param: &fhir::RefineParam<'v>) {
        (self.f)(param).collect_err(&mut self.err);
    }
}

fn visit_refine_params<'a, F>(visit: impl FnOnce(&mut RefineParamVisitor<F>), f: F) -> Result
where
    F: FnMut(&fhir::RefineParam<'a>) -> Result,
{
    let mut visitor = RefineParamVisitor { f, err: None };
    visit(&mut visitor);
    visitor.err.into_result()
}

impl<'genv, 'tcx> ConvPhase<'genv, 'tcx> for Wf<'_, 'genv, 'tcx> {
    /// We don't expand type aliases before sort checking because we need every base type in `fhir`
    /// to match a type in `rty`.
    const EXPAND_TYPE_ALIASES: bool = false;
    const HAS_ELABORATED_INFORMATION: bool = false;

    type Results = InferCtxt<'genv, 'tcx>;

    fn genv(&self) -> GlobalEnv<'genv, 'tcx> {
        self.infcx.genv
    }

    fn owner(&self) -> FluxOwnerId {
        self.infcx.wfckresults.owner
    }

    fn next_sort_vid(&mut self) -> rty::SortVid {
        self.infcx.next_sort_vid(Default::default())
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
        self.infcx
    }

    fn insert_node_sort(&mut self, fhir_id: FhirId, sort: rty::Sort) {
        self.infcx.insert_node_sort(fhir_id, sort);
    }

    fn insert_path_args(&mut self, fhir_id: FhirId, args: rty::GenericArgs) {
        self.infcx.insert_path_args(fhir_id, args);
    }

    fn insert_alias_reft_sort(&mut self, fhir_id: FhirId, fsort: rty::FuncSort) {
        self.infcx.insert_sort_for_alias_reft(fhir_id, fsort);
    }
}

/// The purpose of doing conversion before sort checking is to collect the sorts of base types.
/// Thus, what we return here mostly doesn't matter because the refinements on a type should not
/// affect its sort. The one exception is the sort we generate for refinement parameters.
///
/// For instance, consider the following definition where we refine a struct with a polymorphic set:
/// ```ignore
/// #[flux::refined_by(elems: Set<T>)]
/// struct RSet<T> { ... }
/// ```
/// Now, consider the type `RSet<i32{v: v >= 0}>`. This type desugars to `RSet<λv:σ. {i32[v] | v >= 0}>`
/// where the sort `σ` needs to be inferred. The type `RSet<λv:σ. {i32[v] | v >= 0}>` has sort
/// `RSet<σ>` where `RSet` is the sort-level representation of the `RSet` type. Thus, it is important
/// that the inference variable we generate for `σ` is the same we use for sort checking.
impl WfckResultsProvider for InferCtxt<'_, '_> {
    fn bin_op_sort(&self, _: FhirId) -> rty::Sort {
        rty::Sort::Err
    }

    fn coercions_for(&self, _: FhirId) -> &[rty::Coercion] {
        &[]
    }

    fn field_proj(&self, _: FhirId) -> rty::FieldProj {
        rty::FieldProj::Tuple { arity: 0, field: 0 }
    }

    fn record_ctor(&self, _: FhirId) -> DefId {
        DefId { index: DefIndex::from_u32(0), krate: CrateNum::from_u32(0) }
    }

    fn param_sort(&self, param_id: fhir::ParamId) -> rty::Sort {
        self.param_sort(param_id)
    }

    fn node_sort(&self, _: FhirId) -> rty::Sort {
        rty::Sort::Err
    }

    fn node_sort_args(&self, _: FhirId) -> rty::List<rty::SortArg> {
        rty::List::empty()
    }
}
