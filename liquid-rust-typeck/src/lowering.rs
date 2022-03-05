use crate::ty;
use liquid_rust_common::index::IndexGen;
use liquid_rust_core::ty as core;
use rustc_hash::FxHashMap;

pub struct LoweringCtxt {
    name_map: FxHashMap<core::Name, ty::Name>,
}

impl LoweringCtxt {
    pub fn empty() -> Self {
        Self { name_map: FxHashMap::default() }
    }

    pub fn lower_fn_sig(fn_sig: core::FnSig) -> ty::Binders<ty::FnSig> {
        let name_gen = IndexGen::new();
        let fresh_kvar =
            &mut |_: &ty::BaseTy| unreachable!("inference predicate in top level function");

        let mut cx = LoweringCtxt::empty();

        let params = cx.lower_params(&name_gen, &fn_sig.params);

        let mut requires = vec![];
        for constr in fn_sig.requires {
            requires.push(cx.lower_constr(&constr, fresh_kvar));
        }

        let mut args = vec![];
        for ty in fn_sig.args {
            args.push(cx.lower_ty(&ty, fresh_kvar));
        }

        let mut ensures = vec![];
        for constr in fn_sig.ensures {
            ensures.push(cx.lower_constr(&constr, fresh_kvar));
        }

        let ret = cx.lower_ty(&fn_sig.ret, fresh_kvar);

        ty::Binders::new(params, ty::FnSig { requires, args, ret, ensures })
    }

    pub fn lower_adt_def(adt_def: core::AdtDef) -> ty::AdtDef {
        let mut fresh_kvar = |_: &ty::BaseTy| panic!("inference predicate in top item");
        let name_gen = IndexGen::new();
        let mut cx = LoweringCtxt::empty();

        let refined_by = cx.lower_params(&name_gen, adt_def.refined_by());

        match adt_def {
            core::AdtDef::Transparent { fields, .. } => {
                let fields = fields
                    .into_iter()
                    .map(|ty| cx.lower_ty(&ty, &mut fresh_kvar))
                    .collect();
                ty::AdtDef::Transparent { refined_by, fields }
            }
            core::AdtDef::Opaque { .. } => ty::AdtDef::Opaque { refined_by },
        }
    }

    fn lower_constr(
        &self,
        constr: &core::Constr,
        fresh_kvar: &mut impl FnMut(&ty::BaseTy) -> ty::Pred,
    ) -> ty::Constr {
        match constr {
            core::Constr::Type(loc, ty) => {
                ty::Constr::Type(
                    ty::Loc::Abstract(self.name_map[&loc.name]),
                    self.lower_ty(ty, fresh_kvar),
                )
            }
            core::Constr::Pred(e) => ty::Constr::Pred(self.lower_expr(e)),
        }
    }

    fn lower_params(
        &mut self,
        name_gen: &IndexGen<ty::Name>,
        params: &[core::Param],
    ) -> Vec<ty::Param> {
        params
            .iter()
            .map(|param| {
                let fresh = name_gen.fresh();
                self.name_map.insert(param.name.name, fresh);
                ty::Param { name: fresh, sort: lower_sort(param.sort) }
            })
            .collect()
    }

    pub fn lower_ty(
        &self,
        ty: &core::Ty,
        fresh_kvar: &mut impl FnMut(&ty::BaseTy) -> ty::Pred,
    ) -> ty::Ty {
        match ty {
            core::Ty::Refine(bty, refine) => {
                let refine = ty::Expr::tuple(refine.exprs.iter().map(|e| self.lower_expr(e)));
                ty::Ty::refine(self.lower_base_ty(bty, fresh_kvar), refine)
            }
            core::Ty::Exists(bty, pred) => {
                let bty = self.lower_base_ty(bty, fresh_kvar);
                let pred = match pred {
                    core::Pred::Infer => fresh_kvar(&bty),
                    core::Pred::Expr(e) => ty::Pred::Expr(self.lower_expr(e)),
                };
                ty::Ty::exists(bty, pred)
            }
            core::Ty::StrgRef(loc) => ty::Ty::strg_ref(ty::Loc::Abstract(self.name_map[&loc.name])),
            core::Ty::WeakRef(ty) => ty::Ty::weak_ref(self.lower_ty(ty, fresh_kvar)),
            core::Ty::ShrRef(ty) => ty::Ty::shr_ref(self.lower_ty(ty, fresh_kvar)),
            core::Ty::Param(param) => ty::Ty::param(*param),
            core::Ty::Float(float_ty) => ty::Ty::float(*float_ty),
        }
    }

    fn lower_base_ty(
        &self,
        bty: &core::BaseTy,
        fresh_kvar: &mut impl FnMut(&ty::BaseTy) -> ty::Pred,
    ) -> ty::BaseTy {
        match bty {
            core::BaseTy::Int(int_ty) => ty::BaseTy::Int(*int_ty),
            core::BaseTy::Uint(uint_ty) => ty::BaseTy::Uint(*uint_ty),
            core::BaseTy::Bool => ty::BaseTy::Bool,
            core::BaseTy::Adt(did, substs) => {
                let substs = substs
                    .iter()
                    .map(|ty| self.lower_ty(ty, fresh_kvar))
                    .collect();
                ty::BaseTy::Adt(*did, substs)
            }
        }
    }

    fn lower_expr(&self, expr: &core::Expr) -> ty::Expr {
        match &expr.kind {
            core::ExprKind::Var(var, ..) => ty::Expr::var(self.lower_var(*var)),
            core::ExprKind::Literal(lit) => ty::Expr::constant(self.lower_lit(*lit)),
            core::ExprKind::BinaryOp(op, e1, e2) => {
                ty::Expr::binary_op(lower_bin_op(*op), self.lower_expr(e1), self.lower_expr(e2))
            }
        }
    }

    fn lower_var(&self, var: core::Var) -> ty::Var {
        match var {
            core::Var::Bound => ty::Var::Bound,
            core::Var::Free(name) => ty::Var::Free(self.name_map[&name]),
        }
    }

    fn lower_lit(&self, lit: core::Lit) -> ty::Constant {
        match lit {
            core::Lit::Int(n) => ty::Constant::from(n),
            core::Lit::Bool(b) => ty::Constant::from(b),
        }
    }
}

pub fn lower_sort(sort: core::Sort) -> ty::Sort {
    match sort {
        core::Sort::Int => ty::Sort::int(),
        core::Sort::Bool => ty::Sort::bool(),
        core::Sort::Loc => ty::Sort::loc(),
    }
}

fn lower_bin_op(op: core::BinOp) -> ty::BinOp {
    match op {
        core::BinOp::Iff => ty::BinOp::Iff,
        core::BinOp::Imp => ty::BinOp::Imp,
        core::BinOp::Or => ty::BinOp::Or,
        core::BinOp::And => ty::BinOp::And,
        core::BinOp::Eq => ty::BinOp::Eq,
        core::BinOp::Gt => ty::BinOp::Gt,
        core::BinOp::Ge => ty::BinOp::Ge,
        core::BinOp::Lt => ty::BinOp::Lt,
        core::BinOp::Le => ty::BinOp::Le,
        core::BinOp::Add => ty::BinOp::Add,
        core::BinOp::Sub => ty::BinOp::Sub,
        core::BinOp::Mod => ty::BinOp::Mod,
        core::BinOp::Mul => ty::BinOp::Mul,
    }
}
