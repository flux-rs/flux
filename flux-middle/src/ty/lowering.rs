use crate::{
    global_env::GlobalEnv,
    ty::{self, DebruijnIndex},
};
use flux_common::index::IndexGen;
use itertools::Itertools;
use rustc_hash::FxHashMap;

use crate::core;

pub struct LoweringCtxt<'a, 'genv, 'tcx> {
    genv: &'a GlobalEnv<'genv, 'tcx>,
    name_map: NameMap,
}

#[derive(Default, Debug)]
struct NameMap {
    map: FxHashMap<core::Name, Entry>,
}

#[derive(Copy, Clone, Debug)]
enum Entry {
    Bound { level: u32, index: usize },
    Free(ty::Name),
}

impl From<ty::Name> for Entry {
    fn from(v: ty::Name) -> Self {
        Self::Free(v)
    }
}

impl NameMap {
    fn insert(&mut self, name: core::Name, var: impl Into<Entry>) {
        self.map.insert(name, var.into());
    }

    fn get(&self, name: core::Name, nbinders: u32) -> ty::Expr {
        match self.map[&name] {
            Entry::Bound { level, index } => {
                ty::Expr::bvar(ty::BoundVar::new(index, DebruijnIndex::new(nbinders - level - 1)))
            }
            Entry::Free(name) => ty::Expr::fvar(name),
        }
    }

    fn with_binders<R>(
        &mut self,
        binders: &[core::Ident],
        nbinders: u32,
        f: impl FnOnce(&mut Self, u32) -> R,
    ) -> R {
        for (index, binder) in binders.iter().enumerate() {
            self.insert(binder.name, Entry::Bound { index, level: nbinders });
        }
        let r = f(self, nbinders + 1);
        for binder in binders {
            self.map.remove(&binder.name);
        }
        r
    }
}

impl<'a, 'genv, 'tcx> LoweringCtxt<'a, 'genv, 'tcx> {
    pub fn new(genv: &'a GlobalEnv<'genv, 'tcx>) -> Self {
        Self { genv, name_map: NameMap::default() }
    }

    pub fn lower_const_sig(genv: &GlobalEnv, const_sig: core::ConstSig) -> ty::ConstSig {
        let mut cx = LoweringCtxt::new(genv);
        // cx.lower_ty(&const_sig, 1)
        todo!("lower_const_sig")
    }

    pub fn lower_fn_sig(genv: &GlobalEnv, fn_sig: core::FnSig) -> ty::Binders<ty::FnSig> {
        let mut cx = LoweringCtxt::new(genv);

        let params = cx.lower_params(&fn_sig.params);

        let mut requires = vec![];
        for constr in fn_sig.requires {
            requires.push(cx.lower_constr(&constr, 1));
        }

        let mut args = vec![];
        for ty in fn_sig.args {
            args.push(cx.lower_ty(&ty, 1));
        }

        let mut ensures = vec![];
        for constr in fn_sig.ensures {
            ensures.push(cx.lower_constr(&constr, 1));
        }

        let ret = cx.lower_ty(&fn_sig.ret, 1);

        ty::Binders::new(ty::FnSig::new(requires, args, ret, ensures), params)
    }

    pub(crate) fn lower_struct_def(
        genv: &GlobalEnv,
        struct_def: &core::StructDef,
    ) -> Option<ty::VariantDef> {
        let mut cx = LoweringCtxt::new(genv);
        let sorts = cx.lower_params(&struct_def.refined_by);
        if let core::StructKind::Transparent { fields } = &struct_def.kind {
            let fields = fields.iter().map(|ty| cx.lower_ty(ty, 1)).collect_vec();

            let substs = genv
                .tcx
                .generics_of(struct_def.def_id)
                .params
                .iter()
                .map(|param| ty::Ty::param(ty::ParamTy { index: param.index, name: param.name }))
                .collect_vec();

            let idxs = sorts
                .iter()
                .enumerate()
                .map(|(idx, _)| ty::Expr::bvar(ty::BoundVar::innermost(idx)).into())
                .collect_vec();
            let ret = ty::Ty::indexed(
                ty::BaseTy::adt(ty::AdtDef::new(struct_def.def_id, sorts), substs),
                idxs,
            );

            let variant = ty::VariantDef::new(fields, ret);
            Some(variant)
        } else {
            None
        }
    }

    fn lower_params(&mut self, params: &[core::Param]) -> Vec<ty::Sort> {
        params
            .iter()
            .enumerate()
            .map(|(index, param)| {
                self.name_map
                    .insert(param.name.name, Entry::Bound { index, level: 0 });
                lower_sort(param.sort)
            })
            .collect()
    }

    fn lower_constr(&mut self, constr: &core::Constraint, nbinders: u32) -> ty::Constraint {
        match constr {
            core::Constraint::Type(loc, ty) => {
                ty::Constraint::Type(
                    self.name_map
                        .get(loc.name, nbinders)
                        .to_path()
                        .expect("expected a valid path"),
                    self.lower_ty(ty, nbinders),
                )
            }
            core::Constraint::Pred(e) => ty::Constraint::Pred(lower_expr(e, &self.name_map, 1)),
        }
    }

    pub fn lower_qualifer(qualifier: &core::Qualifier) -> ty::Qualifier {
        let mut name_map = NameMap::default();
        let name_gen = IndexGen::new();

        let args = qualifier
            .args
            .iter()
            .map(|param| {
                let fresh = name_gen.fresh();
                name_map.insert(param.name.name, fresh);
                (fresh, lower_sort(param.sort))
            })
            .collect_vec();

        let expr = lower_expr(&qualifier.expr, &name_map, 1);

        ty::Qualifier { name: qualifier.name.clone(), args, expr }
    }

    pub fn lower_ty(&mut self, ty: &core::Ty, nbinders: u32) -> ty::Ty {
        match ty {
            core::Ty::BaseTy(bty) => {
                let bty = self.lower_base_ty(bty, nbinders);
                let pred = ty::Binders::new(ty::Pred::tt(), bty.sorts());
                ty::Ty::exists(bty, pred)
            }
            core::Ty::Indexed(bty, indices) => {
                let indices = indices
                    .indices
                    .iter()
                    .map(|idx| self.lower_index(idx, nbinders))
                    .collect_vec();
                ty::Ty::indexed(self.lower_base_ty(bty, nbinders), indices)
            }
            core::Ty::Exists(bty, binders, pred) => {
                let bty = self.lower_base_ty(bty, nbinders);
                self.name_map
                    .with_binders(binders, nbinders, |name_map, nbinders| {
                        let expr = lower_expr(pred, name_map, nbinders);
                        let pred = ty::Binders::new(ty::Pred::Expr(expr), bty.sorts());
                        ty::Ty::exists(bty, pred)
                    })
            }
            core::Ty::Ptr(loc) => {
                ty::Ty::ptr(
                    self.name_map
                        .get(loc.name, nbinders)
                        .to_path()
                        .expect("expected a valid path"),
                )
            }
            core::Ty::Ref(rk, ty) => {
                ty::Ty::mk_ref(Self::lower_ref_kind(*rk), self.lower_ty(ty, nbinders))
            }
            core::Ty::Param(param) => ty::Ty::param(*param),
            core::Ty::Float(float_ty) => ty::Ty::float(*float_ty),
            core::Ty::Tuple(tys) => {
                let tys = tys
                    .iter()
                    .map(|ty| self.lower_ty(ty, nbinders))
                    .collect_vec();
                ty::Ty::tuple(tys)
            }
            core::Ty::Never => ty::Ty::never(),
            core::Ty::Constr(pred, ty) => {
                let pred = lower_expr(pred, &self.name_map, nbinders);
                ty::Ty::constr(pred, self.lower_ty(ty, nbinders))
            }
        }
    }

    fn lower_index(&self, idx: &core::Index, nbinders: u32) -> ty::Index {
        ty::Index {
            expr: lower_expr(&idx.expr, &self.name_map, nbinders),
            is_binder: idx.is_binder,
        }
    }

    fn lower_ref_kind(rk: core::RefKind) -> ty::RefKind {
        match rk {
            core::RefKind::Mut => ty::RefKind::Mut,
            core::RefKind::Shr => ty::RefKind::Shr,
        }
    }

    fn lower_base_ty(&mut self, bty: &core::BaseTy, nbinders: u32) -> ty::BaseTy {
        match bty {
            core::BaseTy::Int(int_ty) => ty::BaseTy::Int(*int_ty),
            core::BaseTy::Uint(uint_ty) => ty::BaseTy::Uint(*uint_ty),
            core::BaseTy::Bool => ty::BaseTy::Bool,
            core::BaseTy::Adt(did, substs) => {
                let adt_def = self.genv.adt_def(*did);
                let substs = substs.iter().map(|ty| self.lower_ty(ty, nbinders));
                ty::BaseTy::adt(adt_def, substs)
            }
        }
    }
}

fn lower_expr(expr: &core::Expr, name_map: &NameMap, nbinders: u32) -> ty::Expr {
    match &expr.kind {
        core::ExprKind::Var(name, ..) => name_map.get(*name, nbinders),
        core::ExprKind::Literal(lit) => ty::Expr::constant(lower_lit(*lit)),
        core::ExprKind::BinaryOp(op, e1, e2) => {
            ty::Expr::binary_op(
                *op,
                lower_expr(e1, name_map, nbinders),
                lower_expr(e2, name_map, nbinders),
            )
        }
    }
}

fn lower_lit(lit: core::Lit) -> ty::Constant {
    match lit {
        core::Lit::Int(n) => ty::Constant::from(n),
        core::Lit::Bool(b) => ty::Constant::from(b),
    }
}

pub fn lower_sort(sort: core::Sort) -> ty::Sort {
    match sort {
        core::Sort::Int => ty::Sort::Int,
        core::Sort::Bool => ty::Sort::Bool,
        core::Sort::Loc => ty::Sort::Loc,
    }
}
