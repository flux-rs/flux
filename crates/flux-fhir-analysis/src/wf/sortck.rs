use std::iter;

use derive_where::derive_where;
use ena::unify::InPlaceUnificationTable;
use flux_common::{bug, iter::IterExt, span_bug, tracked_span_bug};
use flux_errors::{ErrorGuaranteed, Errors};
use flux_infer::projections::NormalizeExt;
use flux_middle::{
    fhir::{self, FhirId, FluxOwnerId, QPathExpr, visit::Visitor as _},
    global_env::GlobalEnv,
    queries::QueryResult,
    rty::{
        self, AdtSortDef, FuncSort, List, WfckResults,
        fold::{FallibleTypeFolder, TypeFoldable, TypeFolder, TypeSuperFoldable},
    },
};
use itertools::{Itertools, izip};
use rustc_data_structures::unord::UnordMap;
use rustc_errors::Diagnostic;
use rustc_hash::FxHashMap;
use rustc_hir::def::DefKind;
use rustc_middle::ty::TypingMode;
use rustc_span::{Span, def_id::DefId, symbol::Ident};

use super::errors;
use crate::rustc_infer::infer::TyCtxtInferExt;

type Result<T = ()> = std::result::Result<T, ErrorGuaranteed>;

pub(super) struct InferCtxt<'genv, 'tcx> {
    pub genv: GlobalEnv<'genv, 'tcx>,
    pub owner: FluxOwnerId,
    pub wfckresults: WfckResults,
    sort_unification_table: InPlaceUnificationTable<rty::SortVid>,
    bv_size_unification_table: InPlaceUnificationTable<rty::BvSizeVid>,
    params: FxHashMap<fhir::ParamId, (fhir::RefineParam<'genv>, rty::Sort)>,
    node_sort: FxHashMap<FhirId, rty::Sort>,
    path_args: UnordMap<FhirId, rty::GenericArgs>,
    sort_of_alias_reft: FxHashMap<FhirId, rty::FuncSort>,
    sort_of_literal: NodeMap<'genv, rty::Sort>,
    sort_of_bin_op: NodeMap<'genv, rty::Sort>,
    sort_args_of_app: NodeMap<'genv, List<rty::SortArg>>,
}

pub fn prim_op_sort(op: &fhir::BinOp) -> Option<(Vec<rty::Sort>, rty::Sort)> {
    match op {
        fhir::BinOp::BitAnd
        | fhir::BinOp::BitOr
        | fhir::BinOp::BitXor
        | fhir::BinOp::BitShl
        | fhir::BinOp::BitShr => Some((vec![rty::Sort::Int, rty::Sort::Int], rty::Sort::Int)),
        _ => None,
    }
}

impl<'genv, 'tcx> InferCtxt<'genv, 'tcx> {
    pub(super) fn new(genv: GlobalEnv<'genv, 'tcx>, owner: FluxOwnerId) -> Self {
        // We skip 0 because that's used for sort dummy self types during conv.
        let mut sort_unification_table = InPlaceUnificationTable::new();
        sort_unification_table.new_key(Default::default());
        Self {
            genv,
            owner,
            wfckresults: WfckResults::new(owner),
            sort_unification_table,
            bv_size_unification_table: InPlaceUnificationTable::new(),
            params: Default::default(),
            node_sort: Default::default(),
            path_args: Default::default(),
            sort_of_alias_reft: Default::default(),
            sort_of_literal: Default::default(),
            sort_of_bin_op: Default::default(),
            sort_args_of_app: Default::default(),
        }
    }

    fn check_abs(
        &mut self,
        expr: &fhir::Expr<'genv>,
        params: &[fhir::RefineParam],
        body: &fhir::Expr<'genv>,
        expected: &rty::Sort,
    ) -> Result {
        let Some(fsort) = self.is_coercible_from_func(expected, expr.fhir_id) else {
            return Err(self.emit_err(errors::UnexpectedFun::new(expr.span, expected)));
        };

        let fsort = fsort.expect_mono();

        if params.len() != fsort.inputs().len() {
            return Err(self.emit_err(errors::ParamCountMismatch::new(
                expr.span,
                fsort.inputs().len(),
                params.len(),
            )));
        }
        iter::zip(params, fsort.inputs()).try_for_each_exhaust(|(param, expected)| {
            let found = self.param_sort(param.id);
            if self.try_equate(&found, expected).is_none() {
                return Err(self.emit_sort_mismatch(param.span, expected, &found));
            }
            Ok(())
        })?;
        self.check_expr(body, fsort.output())?;
        self.wfckresults
            .node_sorts_mut()
            .insert(body.fhir_id, fsort.output().clone());
        Ok(())
    }

    fn check_field_exprs(
        &mut self,
        expr_span: Span,
        sort_def: &AdtSortDef,
        sort_args: &[rty::Sort],
        field_exprs: &[fhir::FieldExpr<'genv>],
        spread: &Option<&fhir::Spread<'genv>>,
        expected: &rty::Sort,
    ) -> Result {
        let sort_by_field_name = sort_def.struct_variant().sort_by_field_name(sort_args);
        let mut used_fields = FxHashMap::default();
        for expr in field_exprs {
            // make sure that the field is actually a field
            let Some(sort) = sort_by_field_name.get(&expr.ident.name) else {
                return Err(self.emit_err(errors::FieldNotFound::new(expected.clone(), expr.ident)));
            };
            if let Some(old_field) = used_fields.insert(expr.ident.name, expr.ident) {
                return Err(self.emit_err(errors::DuplicateFieldUsed::new(expr.ident, old_field)));
            }
            self.check_expr(&expr.expr, sort)?;
        }
        if let Some(spread) = spread {
            // must check that the spread is of the same sort as the constructor
            self.check_expr(&spread.expr, expected)
        } else if sort_by_field_name.len() != used_fields.len() {
            // emit an error because all fields are not used
            let missing_fields = sort_by_field_name
                .into_keys()
                .filter(|x| !used_fields.contains_key(x))
                .collect();
            Err(self.emit_err(errors::ConstructorMissingFields::new(expr_span, missing_fields)))
        } else {
            Ok(())
        }
    }

    fn check_constructor(
        &mut self,
        expr: &fhir::Expr,
        field_exprs: &[fhir::FieldExpr<'genv>],
        spread: &Option<&fhir::Spread<'genv>>,
        expected: &rty::Sort,
    ) -> Result {
        let expected = self.resolve_vars_if_possible(expected);
        if let rty::Sort::App(rty::SortCtor::Adt(sort_def), sort_args) = &expected {
            self.wfckresults
                .record_ctors_mut()
                .insert(expr.fhir_id, sort_def.did());
            self.check_field_exprs(expr.span, sort_def, sort_args, field_exprs, spread, &expected)?;
            Ok(())
        } else {
            Err(self.emit_err(errors::UnexpectedConstructor::new(expr.span, &expected)))
        }
    }

    fn check_record(
        &mut self,
        arg: &fhir::Expr<'genv>,
        flds: &[fhir::Expr<'genv>],
        expected: &rty::Sort,
    ) -> Result {
        if let rty::Sort::App(rty::SortCtor::Adt(sort_def), sort_args) = expected {
            let sorts = sort_def.struct_variant().field_sorts(sort_args);
            if flds.len() != sorts.len() {
                return Err(self.emit_err(errors::ArgCountMismatch::new(
                    Some(arg.span),
                    String::from("type"),
                    sorts.len(),
                    flds.len(),
                )));
            }
            self.wfckresults
                .record_ctors_mut()
                .insert(arg.fhir_id, sort_def.did());

            izip!(flds, &sorts)
                .map(|(arg, expected)| self.check_expr(arg, expected))
                .try_collect_exhaust()
        } else {
            Err(self.emit_err(errors::ArgCountMismatch::new(
                Some(arg.span),
                String::from("type"),
                1,
                flds.len(),
            )))
        }
    }

    pub(super) fn check_expr(&mut self, expr: &fhir::Expr<'genv>, expected: &rty::Sort) -> Result {
        match &expr.kind {
            fhir::ExprKind::IfThenElse(p, e1, e2) => {
                self.check_expr(p, &rty::Sort::Bool)?;
                self.check_expr(e1, expected)?;
                self.check_expr(e2, expected)?;
            }
            fhir::ExprKind::Abs(params, body) => {
                self.check_abs(expr, params, body, expected)?;
            }
            fhir::ExprKind::Record(fields) => self.check_record(expr, fields, expected)?,
            fhir::ExprKind::Constructor(None, exprs, spread) => {
                self.check_constructor(expr, exprs, spread, expected)?;
            }
            fhir::ExprKind::UnaryOp(..)
            | fhir::ExprKind::SetLiteral(..)
            | fhir::ExprKind::BinaryOp(..)
            | fhir::ExprKind::Dot(..)
            | fhir::ExprKind::App(..)
            | fhir::ExprKind::Alias(..)
            | fhir::ExprKind::Var(..)
            | fhir::ExprKind::Literal(..)
            | fhir::ExprKind::BoundedQuant(..)
            | fhir::ExprKind::Block(..)
            | fhir::ExprKind::Constructor(..)
            | fhir::ExprKind::PrimApp(..) => {
                let found = self.synth_expr(expr)?;
                let found = self.resolve_vars_if_possible(&found);
                let expected = self.resolve_vars_if_possible(expected);
                if !self.is_coercible(&found, &expected, expr.fhir_id) {
                    return Err(self.emit_sort_mismatch(expr.span, &expected, &found));
                }
            }
            fhir::ExprKind::Err(_) => {
                // an error has already been reported so we can just skip
            }
        }
        Ok(())
    }

    pub(super) fn check_loc(&mut self, loc: &fhir::PathExpr) -> Result {
        let found = self.synth_path(loc);
        if found == rty::Sort::Loc {
            Ok(())
        } else {
            Err(self.emit_sort_mismatch(loc.span, &rty::Sort::Loc, &found))
        }
    }

    fn synth_lit(&mut self, lit: fhir::Lit, expr: &fhir::Expr<'genv>) -> rty::Sort {
        match lit {
            fhir::Lit::Int(_, Some(fhir::NumLitKind::Int)) => rty::Sort::Int,
            fhir::Lit::Int(_, Some(fhir::NumLitKind::Real)) => rty::Sort::Real,
            fhir::Lit::Int(_, None) => {
                let sort = self.next_sort_var_with_cstr(rty::SortCstr::NUMERIC);
                self.sort_of_literal.insert(*expr, sort.clone());
                sort
            }
            fhir::Lit::Bool(_) => rty::Sort::Bool,
            fhir::Lit::Str(_) => rty::Sort::Str,
            fhir::Lit::Char(_) => rty::Sort::Char,
        }
    }

    fn synth_prim_app(
        &mut self,
        op: &fhir::BinOp,
        e1: &fhir::Expr<'genv>,
        e2: &fhir::Expr<'genv>,
        span: Span,
    ) -> Result<rty::Sort> {
        let Some((inputs, output)) = prim_op_sort(op) else {
            return Err(self.emit_err(errors::UnsupportedPrimOp::new(span, *op)));
        };
        let [sort1, sort2] = &inputs[..] else {
            return Err(self.emit_err(errors::ArgCountMismatch::new(
                Some(span),
                String::from("primop app"),
                inputs.len(),
                2,
            )));
        };
        self.check_expr(e1, sort1)?;
        self.check_expr(e2, sort2)?;
        Ok(output)
    }

    fn synth_expr(&mut self, expr: &fhir::Expr<'genv>) -> Result<rty::Sort> {
        match expr.kind {
            fhir::ExprKind::Var(QPathExpr::Resolved(path, _)) => Ok(self.synth_path(&path)),
            fhir::ExprKind::Var(QPathExpr::TypeRelative(..)) => {
                Ok(self.synth_type_relative_path(expr))
            }
            fhir::ExprKind::Literal(lit) => Ok(self.synth_lit(lit, expr)),
            fhir::ExprKind::BinaryOp(op, e1, e2) => self.synth_binary_op(expr, op, e1, e2),
            fhir::ExprKind::PrimApp(op, e1, e2) => self.synth_prim_app(&op, e1, e2, expr.span),
            fhir::ExprKind::UnaryOp(op, e) => self.synth_unary_op(op, e),
            fhir::ExprKind::App(callee, args) => {
                let sort = self.ensure_resolved_path(&callee)?;
                let Some(poly_fsort) = self.is_coercible_to_func(&sort, callee.fhir_id) else {
                    return Err(self.emit_err(errors::ExpectedFun::new(callee.span, &sort)));
                };
                let fsort = self.instantiate_func_sort(expr, poly_fsort);
                self.synth_app(fsort, args, expr.span)
            }
            fhir::ExprKind::BoundedQuant(.., body) => {
                self.check_expr(body, &rty::Sort::Bool)?;
                Ok(rty::Sort::Bool)
            }
            fhir::ExprKind::Alias(_alias_reft, args) => {
                // To check the application we only need the sort of `_alias_reft` which we collected
                // during early conv, but should we do any extra checks on `_alias_reft`?
                let fsort = self.sort_of_alias_reft(expr.fhir_id);
                self.synth_app(fsort, args, expr.span)
            }
            fhir::ExprKind::IfThenElse(p, e1, e2) => {
                self.check_expr(p, &rty::Sort::Bool)?;
                let sort = self.synth_expr(e1)?;
                self.check_expr(e2, &sort)?;
                Ok(sort)
            }
            fhir::ExprKind::Dot(base, fld) => {
                let sort = self.synth_expr(base)?;
                let sort = self
                    .fully_resolve(&sort)
                    .map_err(|_| self.emit_err(errors::CannotInferSort::new(base.span)))?;
                match &sort {
                    rty::Sort::App(rty::SortCtor::Adt(sort_def), sort_args) => {
                        let (proj, sort) = sort_def
                            .struct_variant()
                            .field_by_name(sort_def.did(), sort_args, fld.name)
                            .ok_or_else(|| self.emit_field_not_found(&sort, fld))?;
                        self.wfckresults
                            .field_projs_mut()
                            .insert(expr.fhir_id, proj);
                        Ok(sort)
                    }
                    rty::Sort::Bool | rty::Sort::Int | rty::Sort::Real => {
                        Err(self.emit_err(errors::InvalidPrimitiveDotAccess::new(&sort, fld)))
                    }
                    _ => Err(self.emit_field_not_found(&sort, fld)),
                }
            }
            fhir::ExprKind::Constructor(Some(path), field_exprs, spread) => {
                // if we have S then we can synthesize otherwise we fail
                // first get the sort based on the path - for example S { ... } => S
                // and we should expect sort to be a struct or enum app
                let path_def_id = match path.res {
                    fhir::Res::Def(DefKind::Enum | DefKind::Struct, def_id) => def_id,
                    _ => span_bug!(expr.span, "unexpected path in constructor"),
                };
                let sort_def = self
                    .genv
                    .adt_sort_def_of(path_def_id)
                    .map_err(|e| self.emit_err(e))?;
                // generate fresh inferred sorts for each param
                let fresh_args: rty::List<_> = (0..sort_def.param_count())
                    .map(|_| self.next_sort_var())
                    .collect();
                let sort = rty::Sort::App(rty::SortCtor::Adt(sort_def.clone()), fresh_args.clone());
                // check fields & spread against fresh args
                self.check_field_exprs(
                    expr.span,
                    &sort_def,
                    &fresh_args,
                    field_exprs,
                    &spread,
                    &sort,
                )?;
                Ok(sort)
            }
            fhir::ExprKind::Block(decls, body) => {
                for decl in decls {
                    self.check_expr(&decl.init, &self.param_sort(decl.param.id))?;
                }
                self.synth_expr(body)
            }
            fhir::ExprKind::SetLiteral(elems) => {
                let elem_sort = self.next_sort_var();
                for elem in elems {
                    self.check_expr(elem, &elem_sort)?;
                }
                Ok(rty::Sort::App(rty::SortCtor::Set, List::singleton(elem_sort)))
            }
            _ => Err(self.emit_err(errors::CannotInferSort::new(expr.span))),
        }
    }

    fn synth_path(&mut self, path: &fhir::PathExpr) -> rty::Sort {
        self.node_sort
            .get(&path.fhir_id)
            .unwrap_or_else(|| tracked_span_bug!("no sort found for path: `{path:?}`"))
            .clone()
    }

    fn synth_type_relative_path(&mut self, expr: &fhir::Expr) -> rty::Sort {
        self.node_sort
            .get(&expr.fhir_id)
            .unwrap_or_else(|| tracked_span_bug!("no sort found for: `{expr:?}`"))
            .clone()
    }

    fn synth_binary_op(
        &mut self,
        expr: &fhir::Expr<'genv>,
        op: fhir::BinOp,
        e1: &fhir::Expr<'genv>,
        e2: &fhir::Expr<'genv>,
    ) -> Result<rty::Sort> {
        match op {
            fhir::BinOp::Or | fhir::BinOp::And | fhir::BinOp::Iff | fhir::BinOp::Imp => {
                self.check_expr(e1, &rty::Sort::Bool)?;
                self.check_expr(e2, &rty::Sort::Bool)?;
                Ok(rty::Sort::Bool)
            }
            fhir::BinOp::Eq | fhir::BinOp::Ne => {
                let sort = self.next_sort_var();
                self.check_expr(e1, &sort)?;
                self.check_expr(e2, &sort)?;
                Ok(rty::Sort::Bool)
            }
            fhir::BinOp::Lt | fhir::BinOp::Le | fhir::BinOp::Gt | fhir::BinOp::Ge => {
                let sort = self.next_sort_var();
                self.check_expr(e1, &sort)?;
                self.check_expr(e2, &sort)?;
                self.sort_of_bin_op.insert(*expr, sort.clone());
                Ok(rty::Sort::Bool)
            }
            fhir::BinOp::Add
            | fhir::BinOp::Sub
            | fhir::BinOp::Mul
            | fhir::BinOp::Div
            | fhir::BinOp::Mod
            | fhir::BinOp::BitAnd
            | fhir::BinOp::BitOr
            | fhir::BinOp::BitXor
            | fhir::BinOp::BitShl
            | fhir::BinOp::BitShr => {
                let sort = self.next_sort_var_with_cstr(rty::SortCstr::from_bin_op(op));
                self.check_expr(e1, &sort)?;
                self.check_expr(e2, &sort)?;
                self.sort_of_bin_op.insert(*expr, sort.clone());
                Ok(sort)
            }
        }
    }

    fn synth_unary_op(&mut self, op: fhir::UnOp, e: &fhir::Expr<'genv>) -> Result<rty::Sort> {
        match op {
            fhir::UnOp::Not => {
                self.check_expr(e, &rty::Sort::Bool)?;
                Ok(rty::Sort::Bool)
            }
            fhir::UnOp::Neg => {
                self.check_expr(e, &rty::Sort::Int)?;
                Ok(rty::Sort::Int)
            }
        }
    }

    fn synth_app(
        &mut self,
        fsort: FuncSort,
        args: &[fhir::Expr<'genv>],
        span: Span,
    ) -> Result<rty::Sort> {
        if args.len() != fsort.inputs().len() {
            return Err(self.emit_err(errors::ArgCountMismatch::new(
                Some(span),
                String::from("function"),
                fsort.inputs().len(),
                args.len(),
            )));
        }

        iter::zip(args, fsort.inputs())
            .try_for_each_exhaust(|(arg, formal)| self.check_expr(arg, formal))?;

        Ok(fsort.output().clone())
    }

    fn instantiate_func_sort(
        &mut self,
        app_expr: &fhir::Expr<'genv>,
        fsort: rty::PolyFuncSort,
    ) -> rty::FuncSort {
        let args = fsort
            .params()
            .map(|kind| {
                match kind {
                    rty::SortParamKind::Sort => rty::SortArg::Sort(self.next_sort_var()),
                    rty::SortParamKind::BvSize => rty::SortArg::BvSize(self.next_bv_size_var()),
                }
            })
            .collect_vec();
        self.sort_args_of_app
            .insert(*app_expr, List::from_slice(&args));
        fsort.instantiate(&args)
    }

    pub(crate) fn insert_node_sort(&mut self, fhir_id: FhirId, sort: rty::Sort) {
        self.node_sort.insert(fhir_id, sort);
    }

    pub(crate) fn sort_of_bty(&self, bty: &fhir::BaseTy) -> rty::Sort {
        self.node_sort
            .get(&bty.fhir_id)
            .unwrap_or_else(|| tracked_span_bug!("no sort found for bty: `{bty:?}`"))
            .clone()
    }

    pub(crate) fn insert_path_args(&mut self, fhir_id: FhirId, args: rty::GenericArgs) {
        self.path_args.insert(fhir_id, args);
    }

    pub(crate) fn path_args(&self, fhir_id: FhirId) -> rty::GenericArgs {
        self.path_args
            .get(&fhir_id)
            .unwrap_or_else(|| tracked_span_bug!("no entry found for `{fhir_id:?}`"))
            .clone()
    }

    pub(crate) fn insert_sort_for_alias_reft(&mut self, fhir_id: FhirId, fsort: rty::FuncSort) {
        self.sort_of_alias_reft.insert(fhir_id, fsort);
    }

    fn sort_of_alias_reft(&self, fhir_id: FhirId) -> rty::FuncSort {
        self.sort_of_alias_reft
            .get(&fhir_id)
            .unwrap_or_else(|| tracked_span_bug!("no entry found for `{fhir_id:?}`"))
            .clone()
    }

    fn deeply_normalize_sorts<T: TypeFoldable + Clone>(
        genv: GlobalEnv,
        owner: FluxOwnerId,
        t: &T,
    ) -> QueryResult<T> {
        let infcx = genv
            .tcx()
            .infer_ctxt()
            .with_next_trait_solver(true)
            .build(TypingMode::non_body_analysis());
        if let Some(def_id) = owner.def_id() {
            let def_id = genv.maybe_extern_id(def_id).resolved_id();
            t.deeply_normalize_sorts(def_id, genv, &infcx)
        } else {
            Ok(t.clone())
        }
    }

    // FIXME(nilehmann) this is a bit of a hack. We should find a more robust way to do normalization
    // for sort checking, including normalizing projections. [RJ: normalizing_projections is done now]
    // Maybe we can do lazy normalization. Once we do that maybe we can also stop
    // expanding aliases in `ConvCtxt::conv_sort`.
    pub(crate) fn normalize_sorts(&mut self) -> QueryResult {
        for sort in self.node_sort.values_mut() {
            *sort = Self::deeply_normalize_sorts(self.genv, self.owner, sort)?;
        }
        for fsort in self.sort_of_alias_reft.values_mut() {
            *fsort = Self::deeply_normalize_sorts(self.genv, self.owner, fsort)?;
        }
        Ok(())
    }
}

impl<'genv> InferCtxt<'genv, '_> {
    pub(super) fn declare_param(&mut self, param: fhir::RefineParam<'genv>, sort: rty::Sort) {
        self.params.insert(param.id, (param, sort));
    }

    /// Whether a value of `sort1` can be automatically coerced to a value of `sort2`. A value of an
    /// [`rty::SortCtor::Adt`] sort with a single field of sort `s` can be coerced to a value of sort
    /// `s` and vice versa, i.e., we can automatically project the field out of the record or inject
    /// a value into a record.
    fn is_coercible(&mut self, sort1: &rty::Sort, sort2: &rty::Sort, fhir_id: FhirId) -> bool {
        if self.try_equate(sort1, sort2).is_some() {
            return true;
        }

        let mut sort1 = sort1.clone();
        let mut sort2 = sort2.clone();

        let mut coercions = vec![];
        if let Some((def_id, sort)) = self.is_single_field_struct(&sort1) {
            coercions.push(rty::Coercion::Project(def_id));
            sort1 = sort.clone();
        }
        if let Some((def_id, sort)) = self.is_single_field_struct(&sort2) {
            coercions.push(rty::Coercion::Inject(def_id));
            sort2 = sort.clone();
        }
        self.wfckresults.coercions_mut().insert(fhir_id, coercions);
        self.try_equate(&sort1, &sort2).is_some()
    }

    fn is_coercible_from_func(
        &mut self,
        sort: &rty::Sort,
        fhir_id: FhirId,
    ) -> Option<rty::PolyFuncSort> {
        if let rty::Sort::Func(fsort) = sort {
            Some(fsort.clone())
        } else if let Some((def_id, rty::Sort::Func(fsort))) = self.is_single_field_struct(sort) {
            self.wfckresults
                .coercions_mut()
                .insert(fhir_id, vec![rty::Coercion::Inject(def_id)]);
            Some(fsort.clone())
        } else {
            None
        }
    }

    fn is_coercible_to_func(
        &mut self,
        sort: &rty::Sort,
        fhir_id: FhirId,
    ) -> Option<rty::PolyFuncSort> {
        if let rty::Sort::Func(fsort) = sort {
            Some(fsort.clone())
        } else if let Some((def_id, rty::Sort::Func(fsort))) = self.is_single_field_struct(sort) {
            self.wfckresults
                .coercions_mut()
                .insert(fhir_id, vec![rty::Coercion::Project(def_id)]);
            Some(fsort.clone())
        } else {
            None
        }
    }

    fn try_equate(&mut self, sort1: &rty::Sort, sort2: &rty::Sort) -> Option<rty::Sort> {
        let sort1 = self.resolve_vars_if_possible(sort1);
        let sort2 = self.resolve_vars_if_possible(sort2);
        self.try_equate_inner(&sort1, &sort2)
    }

    fn try_equate_inner(&mut self, sort1: &rty::Sort, sort2: &rty::Sort) -> Option<rty::Sort> {
        match (sort1, sort2) {
            (rty::Sort::Infer(vid1), rty::Sort::Infer(vid2)) => {
                self.sort_unification_table
                    .unify_var_var(*vid1, *vid2)
                    .ok()?;
            }
            (rty::Sort::Infer(vid), sort) | (sort, rty::Sort::Infer(vid)) => {
                self.sort_unification_table
                    .unify_var_value(*vid, rty::SortVarVal::Solved(sort.clone()))
                    .ok()?;
            }
            (rty::Sort::App(ctor1, args1), rty::Sort::App(ctor2, args2)) => {
                if ctor1 != ctor2 || args1.len() != args2.len() {
                    return None;
                }
                let mut args = vec![];
                for (s1, s2) in args1.iter().zip(args2.iter()) {
                    args.push(self.try_equate_inner(s1, s2)?);
                }
            }
            (rty::Sort::BitVec(size1), rty::Sort::BitVec(size2)) => {
                self.try_equate_bv_sizes(*size1, *size2)?;
            }
            _ if sort1 == sort2 => {}
            _ => return None,
        }
        Some(sort1.clone())
    }

    fn try_equate_bv_sizes(
        &mut self,
        size1: rty::BvSize,
        size2: rty::BvSize,
    ) -> Option<rty::BvSize> {
        match (size1, size2) {
            (rty::BvSize::Infer(vid1), rty::BvSize::Infer(vid2)) => {
                self.bv_size_unification_table
                    .unify_var_var(vid1, vid2)
                    .ok()?;
            }
            (rty::BvSize::Infer(vid), size) | (size, rty::BvSize::Infer(vid)) => {
                self.bv_size_unification_table
                    .unify_var_value(vid, Some(size))
                    .ok()?;
            }
            _ if size1 == size2 => {}
            _ => return None,
        }
        Some(size1)
    }

    fn next_sort_var(&mut self) -> rty::Sort {
        rty::Sort::Infer(self.next_sort_vid(Default::default()))
    }

    fn next_sort_var_with_cstr(&mut self, cstr: rty::SortCstr) -> rty::Sort {
        rty::Sort::Infer(self.next_sort_vid(rty::SortVarVal::Unsolved(cstr)))
    }

    pub(crate) fn next_sort_vid(&mut self, val: rty::SortVarVal) -> rty::SortVid {
        self.sort_unification_table.new_key(val)
    }

    fn next_bv_size_var(&mut self) -> rty::BvSize {
        rty::BvSize::Infer(self.next_bv_size_vid())
    }

    fn next_bv_size_vid(&mut self) -> rty::BvSizeVid {
        self.bv_size_unification_table.new_key(None)
    }

    fn ensure_resolved_path(&mut self, path: &fhir::PathExpr) -> Result<rty::Sort> {
        let sort = self.synth_path(path);
        self.fully_resolve(&sort)
            .map_err(|_| self.emit_err(errors::CannotInferSort::new(path.span)))
    }

    fn is_single_field_struct(&mut self, sort: &rty::Sort) -> Option<(DefId, rty::Sort)> {
        if let rty::Sort::App(rty::SortCtor::Adt(sort_def), sort_args) = sort
            && let Some(variant) = sort_def.opt_struct_variant()
            && let [sort] = &variant.field_sorts(sort_args)[..]
        {
            Some((sort_def.did(), sort.clone()))
        } else {
            None
        }
    }

    pub(crate) fn into_results(mut self) -> Result<WfckResults> {
        // Make sure the int literals are fully resolved. This must happen before everything else
        // such that we properly apply the fallback for unconstrained num vars.
        for (node, sort) in std::mem::take(&mut self.sort_of_literal) {
            // Fallback to `int` when a num variable is unconstrained. Note that we unconditionally
            // unify the variable. This is fine because if the variable has already been unified,
            // the operation will fail and this won't have any effect. Also note that unifying a
            // variable could solve variables that appear later in this for loop. This is also fine
            // because the order doesn't matter as we are unifying everything to `int`.
            if let rty::Sort::Infer(vid) = &sort {
                let _ = self
                    .sort_unification_table
                    .unify_var_value(*vid, rty::SortVarVal::Solved(rty::Sort::Int));
            }

            let sort = self
                .fully_resolve(&sort)
                .map_err(|_| self.emit_err(errors::CannotInferSort::new(node.span)))?;
            self.wfckresults.node_sorts_mut().insert(node.fhir_id, sort);
        }

        // Make sure the binary operators are fully resolved
        for (node, sort) in std::mem::take(&mut self.sort_of_bin_op) {
            let sort = self
                .fully_resolve(&sort)
                .map_err(|_| self.emit_err(errors::CannotInferSort::new(node.span)))?;
            self.wfckresults
                .bin_op_sorts_mut()
                .insert(node.fhir_id, sort);
        }

        let allow_uninterpreted_cast = self
            .owner
            .def_id()
            .map_or_else(flux_config::allow_uninterpreted_cast, |def_id| {
                self.genv.infer_opts(def_id).allow_uninterpreted_cast
            });

        // Make sure that function applications are fully resolved
        for (node, sort_args) in std::mem::take(&mut self.sort_args_of_app) {
            let mut res = vec![];
            for sort_arg in &sort_args {
                let sort_arg = match sort_arg {
                    rty::SortArg::Sort(sort) => {
                        let sort = self
                            .fully_resolve(sort)
                            .map_err(|_| self.emit_err(errors::CannotInferSort::new(node.span)))?;
                        rty::SortArg::Sort(sort)
                    }
                    rty::SortArg::BvSize(rty::BvSize::Infer(vid)) => {
                        let size = self
                            .bv_size_unification_table
                            .probe_value(*vid)
                            .ok_or_else(|| {
                                self.emit_err(errors::CannotInferSort::new(node.span))
                            })?;
                        rty::SortArg::BvSize(size)
                    }
                    _ => sort_arg.clone(),
                };
                res.push(sort_arg);
            }
            if let fhir::ExprKind::App(callee, _) = node.kind
                && matches!(callee.res, fhir::Res::GlobalFunc(fhir::SpecFuncKind::Cast))
            {
                let [rty::SortArg::Sort(from), rty::SortArg::Sort(to)] = &res[..] else {
                    span_bug!(node.span, "invalid sort args!")
                };
                if !allow_uninterpreted_cast
                    && matches!(from.cast_kind(to), rty::CastKind::Uninterpreted)
                {
                    return Err(self.emit_err(errors::InvalidCast::new(node.span, from, to)));
                }
            }
            self.wfckresults
                .fn_app_sorts_mut()
                .insert(node.fhir_id, res.into());
        }

        // Make sure all parameters are fully resolved
        for (_, (param, sort)) in std::mem::take(&mut self.params) {
            let sort = self
                .fully_resolve(&sort)
                .map_err(|_| self.emit_err(errors::SortAnnotationNeeded::new(&param)))?;
            self.wfckresults.param_sorts_mut().insert(param.id, sort);
        }

        Ok(self.wfckresults)
    }

    pub(crate) fn infer_mode(&self, id: fhir::ParamId) -> fhir::InferMode {
        fhir::InferMode::from_param_kind(self.params[&id].0.kind)
    }

    #[track_caller]
    pub(crate) fn param_sort(&self, id: fhir::ParamId) -> rty::Sort {
        self.params
            .get(&id)
            .unwrap_or_else(|| bug!("no entry found for `{id:?}`"))
            .1
            .clone()
    }

    fn shallow_resolve(&mut self, sort: &rty::Sort) -> rty::Sort {
        sort.fold_with(&mut ShallowResolver { infcx: self })
    }

    fn resolve_vars_if_possible(&mut self, sort: &rty::Sort) -> rty::Sort {
        sort.fold_with(&mut OpportunisticResolver { infcx: self })
    }

    pub(crate) fn fully_resolve(&mut self, sort: &rty::Sort) -> std::result::Result<rty::Sort, ()> {
        sort.try_fold_with(&mut FullResolver { infcx: self })
    }
}

/// Before the main sort inference, we do a first traversal checking all implicitly scoped parameters
/// declared with `@` or `#` and infer their sort based on the type they are indexing, e.g., if `n` was
/// declared as `i32[@n]`, we infer `int` for `n`.
///
/// This prepass is necessary because sometimes the order in which we traverse expressions can
/// affect what we can infer. By resolving implicit parameters first, we ensure more consistent and
/// complete inference regardless of how expressions are later traversed.
///
/// It should be possible to improve sort checking (e.g., by allowing partially resolved sorts in
/// function position) such that we don't need this anymore.
pub(crate) struct ImplicitParamInferer<'a, 'genv, 'tcx> {
    infcx: &'a mut InferCtxt<'genv, 'tcx>,
    errors: Errors<'genv>,
}

impl<'a, 'genv, 'tcx> ImplicitParamInferer<'a, 'genv, 'tcx> {
    pub(crate) fn infer(
        infcx: &'a mut InferCtxt<'genv, 'tcx>,
        node: &fhir::OwnerNode<'genv>,
    ) -> Result {
        let errors = Errors::new(infcx.genv.sess());
        let mut vis = Self { infcx, errors };
        vis.visit_node(node);
        vis.errors.to_result()
    }

    fn infer_implicit_params(&mut self, idx: &fhir::Expr, expected: &rty::Sort) {
        match idx.kind {
            fhir::ExprKind::Var(QPathExpr::Resolved(var, Some(_))) => {
                let (_, id) = var.res.expect_param();
                let found = self.infcx.param_sort(id);
                self.infcx.try_equate(&found, expected).unwrap_or_else(|| {
                    span_bug!(idx.span, "failed to equate sorts: `{found:?}` `{expected:?}`")
                });
            }
            fhir::ExprKind::Record(flds) => {
                if let rty::Sort::App(rty::SortCtor::Adt(sort_def), sort_args) = expected {
                    let sorts = sort_def.struct_variant().field_sorts(sort_args);
                    if flds.len() != sorts.len() {
                        self.errors.emit(errors::ArgCountMismatch::new(
                            Some(idx.span),
                            String::from("type"),
                            sorts.len(),
                            flds.len(),
                        ));
                        return;
                    }
                    for (f, sort) in iter::zip(flds, &sorts) {
                        self.infer_implicit_params(f, sort);
                    }
                } else {
                    self.errors.emit(errors::ArgCountMismatch::new(
                        Some(idx.span),
                        String::from("type"),
                        1,
                        flds.len(),
                    ));
                }
            }
            _ => {}
        }
    }
}

impl<'genv> fhir::visit::Visitor<'genv> for ImplicitParamInferer<'_, 'genv, '_> {
    fn visit_ty(&mut self, ty: &fhir::Ty<'genv>) {
        if let fhir::TyKind::Indexed(bty, idx) = &ty.kind {
            let expected = self.infcx.sort_of_bty(bty);
            self.infer_implicit_params(idx, &expected);
        }
        fhir::visit::walk_ty(self, ty);
    }
}

impl InferCtxt<'_, '_> {
    #[track_caller]
    fn emit_sort_mismatch(
        &mut self,
        span: Span,
        expected: &rty::Sort,
        found: &rty::Sort,
    ) -> ErrorGuaranteed {
        let expected = self.resolve_vars_if_possible(expected);
        let found = self.resolve_vars_if_possible(found);
        self.emit_err(errors::SortMismatch::new(span, expected, found))
    }

    fn emit_field_not_found(&mut self, sort: &rty::Sort, field: Ident) -> ErrorGuaranteed {
        self.emit_err(errors::FieldNotFound::new(sort.clone(), field))
    }

    #[track_caller]
    fn emit_err<'b>(&'b self, err: impl Diagnostic<'b>) -> ErrorGuaranteed {
        self.genv.sess().emit_err(err)
    }
}

struct ShallowResolver<'a, 'genv, 'tcx> {
    infcx: &'a mut InferCtxt<'genv, 'tcx>,
}

impl TypeFolder for ShallowResolver<'_, '_, '_> {
    fn fold_sort(&mut self, sort: &rty::Sort) -> rty::Sort {
        match sort {
            rty::Sort::Infer(vid) => {
                // if `sort` is a sort variable, it can be resolved to a bit-vec variable,
                // which can then be recursively resolved, hence the recursion. Note though that
                // we prevent sort variables from unifying to other sort variables directly (though
                // they may be embedded structurally), so this recursion should always be of very
                // limited depth.
                self.infcx
                    .sort_unification_table
                    .probe_value(*vid)
                    .map_solved(|sort| sort.fold_with(self))
                    .solved_or(sort)
            }
            rty::Sort::BitVec(rty::BvSize::Infer(vid)) => {
                self.infcx
                    .bv_size_unification_table
                    .probe_value(*vid)
                    .map(rty::Sort::BitVec)
                    .unwrap_or(sort.clone())
            }
            _ => sort.clone(),
        }
    }
}

struct OpportunisticResolver<'a, 'genv, 'tcx> {
    infcx: &'a mut InferCtxt<'genv, 'tcx>,
}

impl TypeFolder for OpportunisticResolver<'_, '_, '_> {
    fn fold_sort(&mut self, sort: &rty::Sort) -> rty::Sort {
        let s = self.infcx.shallow_resolve(sort);
        s.super_fold_with(self)
    }
}

struct FullResolver<'a, 'genv, 'tcx> {
    infcx: &'a mut InferCtxt<'genv, 'tcx>,
}

impl FallibleTypeFolder for FullResolver<'_, '_, '_> {
    type Error = ();

    fn try_fold_sort(&mut self, sort: &rty::Sort) -> std::result::Result<rty::Sort, Self::Error> {
        let s = self.infcx.shallow_resolve(sort);
        match s {
            rty::Sort::Infer(_) | rty::Sort::BitVec(rty::BvSize::Infer(_)) => Err(()),
            _ => s.try_super_fold_with(self),
        }
    }
}

/// Map to associate data to a node (i.e., an expression).
///
/// Used to record elaborated information.
#[derive_where(Default)]
struct NodeMap<'genv, T> {
    map: FxHashMap<FhirId, (fhir::Expr<'genv>, T)>,
}

impl<'genv, T> NodeMap<'genv, T> {
    /// Add a `node` to the map with associated `data`
    fn insert(&mut self, node: fhir::Expr<'genv>, data: T) {
        assert!(self.map.insert(node.fhir_id, (node, data)).is_none());
    }
}

impl<'genv, T> IntoIterator for NodeMap<'genv, T> {
    type Item = (fhir::Expr<'genv>, T);

    type IntoIter = std::collections::hash_map::IntoValues<FhirId, Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.map.into_values()
    }
}
