pub mod paths_tree;

use std::iter;

use itertools::{izip, Itertools};

use rustc_hash::{FxHashMap, FxHashSet};
use rustc_middle::ty::TyCtxt;

use liquid_rust_common::index::IndexGen;
use liquid_rust_middle::{
    global_env::GlobalEnv,
    rustc::mir::Place,
    ty::{subst::Subst, BaseTy, Expr, ExprKind, Param, Path, RefKind, Ty, TyKind},
};

use crate::{
    constraint_gen::{ConstraintGen, Tag},
    param_infer,
    pure_ctxt::{PureCtxt, Scope},
};

use self::paths_tree::{LookupResult, PathsTree};

use super::ty::{Loc, Name, Pred, Sort};

#[derive(Clone, Default)]
pub struct TypeEnv {
    bindings: PathsTree,
}

pub struct TypeEnvInfer {
    params: FxHashMap<Name, Sort>,
    scope: Scope,
    name_gen: IndexGen<Name>,
    env: TypeEnv,
}

pub struct BasicBlockEnv {
    pub params: Vec<Param>,
    constrs: Vec<Pred>,
    scope: Scope,
    pub env: TypeEnv,
}

impl TypeEnv {
    pub fn new() -> TypeEnv {
        TypeEnv { bindings: PathsTree::default() }
    }

    pub fn alloc_with_ty(&mut self, loc: impl Into<Loc>, ty: Ty) {
        let loc = loc.into();
        self.bindings.insert(loc, ty);
    }

    pub fn alloc(&mut self, loc: impl Into<Loc>) {
        let loc = loc.into();
        self.bindings.insert(loc, Ty::uninit());
    }

    pub fn into_infer(self, genv: &GlobalEnv, scope: Scope) -> TypeEnvInfer {
        TypeEnvInfer::new(genv, scope, self)
    }

    fn remove(&mut self, loc: Loc) {
        self.bindings.remove(loc);
    }

    #[track_caller]
    pub fn lookup_place(&mut self, pcx: &mut PureCtxt, place: &Place) -> Ty {
        self.bindings
            .lookup_place(pcx, place, |_, result| result.ty())
    }

    #[track_caller]
    pub fn lookup_path(&self, path: &Path) -> Ty {
        self.bindings[path].clone()
    }

    pub fn update_path(&mut self, path: &Path, new_ty: Ty) {
        self.bindings[path] = new_ty;
    }

    // TODO(nilehmann) find a better name for borrow in this context
    // TODO(nilehmann) unify borrow_mut and borrow_shr and return ptr(l)
    pub fn borrow_mut(&mut self, pcx: &mut PureCtxt, place: &Place) -> Ty {
        self.bindings.lookup_place(pcx, place, |_, result| {
            match result {
                LookupResult::Ptr(path, _) => Ty::strg_ref(path),
                LookupResult::Ref(RefKind::Mut, ty) => Ty::mk_ref(RefKind::Mut, ty),
                LookupResult::Ref(RefKind::Shr, _) => {
                    panic!("cannot borrow `{place:?}` as mutable, as it is behind a `&` reference")
                }
            }
        })
    }

    pub fn borrow_shr(&mut self, pcx: &mut PureCtxt, place: &Place) -> Ty {
        self.bindings
            .lookup_place(pcx, place, |_, result| Ty::mk_ref(RefKind::Shr, result.ty()))
    }

    pub fn write_place(
        &mut self,
        genv: &GlobalEnv,
        pcx: &mut PureCtxt,
        place: &Place,
        new_ty: Ty,
        tag: Tag,
    ) {
        self.bindings.lookup_place(pcx, place, |pcx, result| {
            match result {
                LookupResult::Ptr(_, ty) => {
                    *ty = new_ty;
                }
                LookupResult::Ref(RefKind::Mut, ty) => {
                    let mut gen = ConstraintGen::new(genv, pcx.breadcrumb(), tag);
                    gen.subtyping(&new_ty, &ty);
                }
                LookupResult::Ref(RefKind::Shr, _) => {
                    panic!("cannot assign to `{place:?}`, which is behind a `&` reference")
                }
            }
        });
    }

    pub fn move_place(&mut self, pcx: &mut PureCtxt, place: &Place) -> Ty {
        self.bindings.lookup_place(pcx, place, |_, result| {
            match result {
                LookupResult::Ptr(_, ty) => {
                    let old = ty.clone();
                    *ty = Ty::uninit();
                    old
                }
                LookupResult::Ref(RefKind::Mut, _) => {
                    panic!("cannot move out of `{place:?}`, which is behind a `&` reference")
                }
                LookupResult::Ref(RefKind::Shr, _) => {
                    panic!("cannot move out of `{place:?}`, which is behind a `&mut` reference")
                }
            }
        })
    }

    pub fn weaken_ty_at_path(&mut self, gen: &mut ConstraintGen, path: &Path, bound: Ty) {
        let ty = &mut self.bindings[path];
        gen.subtyping(ty, &bound);
        *ty = bound;
    }

    pub fn unpack_ty(&mut self, genv: &GlobalEnv, pcx: &mut PureCtxt, ty: &Ty) -> Ty {
        match ty.kind() {
            TyKind::Exists(bty, p) => {
                let exprs = pcx.push_bindings(&genv.sorts(bty), p);
                Ty::indexed(bty.clone(), exprs)
            }
            TyKind::Ref(RefKind::Shr, ty) => {
                let ty = self.unpack_ty(genv, pcx, ty);
                Ty::mk_ref(RefKind::Shr, ty)
            }
            _ => ty.clone(),
        }
    }

    pub fn unpack(&mut self, genv: &GlobalEnv, pcx: &mut PureCtxt) {
        for path in self.bindings.paths().collect_vec() {
            let ty = self.bindings[&path].clone();
            let ty = self.unpack_ty(genv, pcx, &ty);
            self.bindings[&path] = ty;
        }
    }

    fn infer_subst_for_bb_env(&self, bb_env: &BasicBlockEnv) -> Subst {
        let params = bb_env.params.iter().map(|param| param.name).collect();
        let mut subst = Subst::empty();
        for (path, ty1) in self.bindings.iter() {
            if bb_env.env.bindings.contains_loc(path.loc) {
                let ty2 = &bb_env.env.bindings[&path];
                self.infer_subst_for_bb_env_tys(bb_env, &params, ty1, ty2, &mut subst);
            }
        }

        assert!(param_infer::check_inference(
            &subst,
            bb_env
                .params
                .iter()
                .filter(|param| !param.sort.is_loc())
                .map(|param| param.name)
        )
        .is_ok());
        subst
    }

    fn infer_subst_for_bb_env_tys(
        &self,
        bb_env: &BasicBlockEnv,
        params: &FxHashSet<Name>,
        ty1: &Ty,
        ty2: &Ty,
        subst: &mut Subst,
    ) {
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Indexed(_, exprs1), TyKind::Indexed(_, exprs2)) => {
                for (e1, e2) in iter::zip(exprs1, exprs2) {
                    param_infer::infer_from_exprs(subst, params, e1, e2);
                }
            }
            (TyKind::Ptr(path1), TyKind::Ptr(path2)) => {
                self.infer_subst_for_bb_env_paths(bb_env, params, path1, path2, subst);
                let ty1 = &self.bindings[path1];
                let ty2 = &bb_env.env.bindings[path2];
                self.infer_subst_for_bb_env_tys(bb_env, params, ty1, ty2, subst);
            }
            (TyKind::Ref(mode1, ty1), TyKind::Ref(mode2, ty2)) => {
                debug_assert_eq!(mode1, mode2);
                self.infer_subst_for_bb_env_tys(bb_env, params, ty1, ty2, subst);
            }
            _ => {}
        }
    }

    fn infer_subst_for_bb_env_paths(
        &self,
        bb_env: &BasicBlockEnv,
        _params: &FxHashSet<Name>,
        path1: &Path,
        path2: &Path,
        subst: &mut Subst,
    ) {
        // TODO(nilehmann) we should probably do something with _params
        if !path1.projection().is_empty() || !path2.projection().is_empty() {
            return;
        }
        if let (Loc::Free(loc1), Loc::Free(loc2)) = (path1.loc, path2.loc) {
            if !bb_env.scope.contains(loc1) && !bb_env.scope.contains(loc2) {
                subst.insert(loc2, Path::from(Loc::Free(loc1)));
            }
        }
    }

    pub fn check_goto(
        mut self,
        genv: &GlobalEnv,
        pcx: &mut PureCtxt,
        bb_env: &mut BasicBlockEnv,
        tag: Tag,
    ) {
        self.bindings.fold_unfold_with(pcx, &bb_env.env.bindings);

        // Infer subst
        let subst = self.infer_subst_for_bb_env(bb_env);

        // Check constraints
        let mut gen = ConstraintGen::new(genv, pcx.breadcrumb(), tag);
        for (param, constr) in iter::zip(&bb_env.params, &bb_env.constrs) {
            gen.check_pred(subst.subst_pred(&constr.subst_bound_vars(&[Expr::fvar(param.name)])));
        }

        let goto_env = bb_env.env.clone().subst(&subst);

        // Weakening
        let locs = self
            .bindings
            .locs()
            .filter(|loc| !goto_env.bindings.contains_loc(*loc))
            .collect_vec();
        for loc in locs {
            self.remove(loc);
        }

        // Convert pointers to borrows
        for path in self.bindings.paths().collect_vec() {
            let ty1 = self.bindings[&path].clone();
            let ty2 = goto_env.bindings[&path].clone();
            if let (TyKind::Ptr(ptr_path), TyKind::Ref(RefKind::Mut, bound)) =
                (ty1.kind(), ty2.kind())
            {
                let ty = &self.bindings[ptr_path];
                gen.subtyping(ty, bound);
                self.bindings[ptr_path] = bound.clone();
                self.bindings[&path] = Ty::mk_ref(RefKind::Mut, bound.clone());
            }
        }

        // Check subtyping
        for (path, ty1) in self.bindings.iter_mut() {
            let ty2 = goto_env.bindings[&path].clone();
            gen.subtyping(ty1, &ty2);
            *ty1 = ty2;
        }

        debug_assert!(self.bindings == goto_env.bindings);
    }

    pub fn subst(self, subst: &Subst) -> TypeEnv {
        TypeEnv { bindings: self.bindings.subst(subst) }
    }
}

impl TypeEnvInfer {
    pub fn enter(&self, pcx: &mut PureCtxt) -> TypeEnv {
        let mut subst = Subst::empty();
        // HACK(nilehmann) it is crucial that the order in this iteration is the same as
        // [`TypeEnvInfer::into_bb_env`] otherwise names will be out of order in the checking phase.
        for (name, sort) in self.params.iter() {
            let e = pcx.push_binding(sort.clone(), &Pred::tt());
            subst.insert(*name, e);
        }
        self.env.clone().subst(&subst)
    }

    fn new(genv: &GlobalEnv, scope: Scope, env: TypeEnv) -> TypeEnvInfer {
        let name_gen = scope.name_gen();
        let mut names = FxHashMap::default();
        let mut params = FxHashMap::default();
        let mut env = TypeEnvInfer::pack_refs(&mut params, &scope, &name_gen, env);
        for ty in env.bindings.values_mut() {
            *ty = TypeEnvInfer::pack_ty(&mut params, genv, &scope, &mut names, &name_gen, ty);
        }
        TypeEnvInfer { params, name_gen, env, scope }
    }

    fn pack_refs(
        params: &mut FxHashMap<Name, Sort>,
        scope: &Scope,
        name_gen: &IndexGen<Name>,
        env: TypeEnv,
    ) -> TypeEnv {
        let mut subst = Subst::empty();

        for loc in env.bindings.locs() {
            if let Loc::Free(loc) = loc {
                if !scope.contains(loc) {
                    let fresh = name_gen.fresh();
                    params.insert(fresh, Sort::loc());
                    subst.insert(loc, Path::from(Loc::Free(fresh)));
                }
            }
        }
        env.subst(&subst)
    }

    fn pack_ty(
        params: &mut FxHashMap<Name, Sort>,
        genv: &GlobalEnv,
        scope: &Scope,
        names: &mut FxHashMap<Expr, Name>,
        name_gen: &IndexGen<Name>,
        ty: &Ty,
    ) -> Ty {
        match ty.kind() {
            TyKind::Indexed(bty, exprs) => {
                let sorts = genv.sorts(bty);
                let exprs = exprs
                    .iter()
                    .zip(sorts)
                    .map(|(e, sort)| {
                        let has_free_vars = !scope.contains_all(e.vars());
                        if let Some(name) = names.get(e) {
                            Expr::fvar(*name)
                        } else if has_free_vars {
                            let fresh = name_gen.fresh();
                            params.insert(fresh, sort);
                            names.insert(e.clone(), fresh);
                            Expr::fvar(fresh)
                        } else {
                            e.clone()
                        }
                    })
                    .collect_vec();
                let bty = TypeEnvInfer::pack_bty(params, genv, scope, names, name_gen, bty);
                Ty::indexed(bty, exprs)
            }
            TyKind::Tuple(tys) => {
                let tys = tys
                    .iter()
                    .map(|ty| TypeEnvInfer::pack_ty(params, genv, scope, names, name_gen, ty))
                    .collect_vec();
                Ty::tuple(tys)
            }
            // TODO(nilehmann) [`TyKind::Exists`] could also in theory contains free variables.
            TyKind::Exists(_, _)
            | TyKind::Never
            | TyKind::Discr
            | TyKind::Float(_)
            | TyKind::Ptr(_)
            | TyKind::Uninit
            | TyKind::Ref(..)
            | TyKind::Param(_) => ty.clone(),
        }
    }

    fn pack_bty(
        params: &mut FxHashMap<Name, Sort>,
        genv: &GlobalEnv,
        scope: &Scope,
        names: &mut FxHashMap<Expr, Name>,
        name_gen: &IndexGen<Name>,
        bty: &BaseTy,
    ) -> BaseTy {
        match bty {
            BaseTy::Adt(adt_def, substs) => {
                let substs = substs
                    .iter()
                    .map(|ty| Self::pack_ty(params, genv, scope, names, name_gen, ty));
                BaseTy::adt(adt_def.clone(), substs)
            }
            BaseTy::Int(_) | BaseTy::Uint(_) | BaseTy::Bool => bty.clone(),
        }
    }

    /// join(self, genv, other) consumes the bindings in other, to "update"
    /// 'self' in place, and returns 'true' if there was an actual change
    /// or 'false' indicating no change (i.e. a fixpoint was reached).

    pub fn join(&mut self, genv: &GlobalEnv, mut other: TypeEnv) -> bool {
        // Unfold
        self.env.bindings.unfold_with(&mut other.bindings);

        // Weakening
        let locs = self
            .env
            .bindings
            .locs()
            .filter(|loc| !other.bindings.contains_loc(*loc))
            .collect_vec();
        for loc in locs {
            if let Some(loc) = self.packed_loc(loc) {
                self.params.remove(&loc);
            }
            self.env.remove(loc);
        }

        let paths = self.env.bindings.paths().collect_vec();

        // Convert pointers to borrows
        for path in &paths {
            let ty1 = self.env.bindings[path].clone();
            let ty2 = other.bindings[path].clone();
            match (ty1.kind(), ty2.kind()) {
                (TyKind::Ptr(path1), TyKind::Ptr(path2)) if path1 != path2 => {
                    let ty1 = self.env.bindings[path1].with_holes();
                    let ty2 = other.bindings[path2].with_holes();

                    self.env.bindings[path] = Ty::mk_ref(RefKind::Mut, ty1.clone());
                    other.bindings[path] = Ty::mk_ref(RefKind::Mut, ty2.clone());

                    self.env.bindings[path1] = ty1;
                    other.bindings[path2] = ty2;
                }
                (TyKind::Ptr(ptr_path), TyKind::Ref(RefKind::Mut, bound)) => {
                    self.env.bindings[ptr_path] = bound.clone();
                    self.env.bindings[path] = Ty::mk_ref(RefKind::Mut, bound.clone());
                }
                (TyKind::Ref(RefKind::Mut, bound), TyKind::Ptr(ptr_path)) => {
                    other.bindings[ptr_path] = bound.clone();
                    other.bindings[path] = Ty::mk_ref(RefKind::Mut, bound.clone());
                }
                _ => {}
            }
        }

        // Join types
        let mut modified = false;
        for path in &paths {
            let ty1 = self.env.bindings[path].clone();
            let ty2 = other.bindings[path].clone();
            let ty = self.join_ty(genv, &ty1, &ty2);
            modified |= ty1 != ty;
            self.env.bindings[path] = ty;
        }

        self.remove_dead_params();

        modified
    }

    fn remove_dead_params(&mut self) {
        let dead_names = self.dead_params();
        for x in dead_names.iter() {
            self.params.remove(x);
        }
    }

    /// 'dead_params' returns the (ideally empty) subset of 'self.params' comprising
    /// names that do not appear in types in 'env' (in a way that makes for easy solving).
    fn dead_params(&self) -> Vec<Name> {
        let mut used: FxHashSet<Name> = FxHashSet::default();
        for (_, ty) in self.env.bindings.iter() {
            for x in ty.vars().iter() {
                used.insert(*x);
            }
        }
        self.params
            .iter()
            .filter(|(x, _)| !used.contains(x))
            .map(|(x, _)| *x)
            .collect()
    }

    fn join_ty(&mut self, genv: &GlobalEnv, ty1: &Ty, ty2: &Ty) -> Ty {
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Uninit, _) | (_, TyKind::Uninit) => Ty::uninit(),
            (TyKind::Ptr(path1), TyKind::Ptr(path2)) => {
                debug_assert_eq!(path1, path2);
                Ty::strg_ref(path1.clone())
            }
            (TyKind::Indexed(bty1, exprs1), TyKind::Indexed(bty2, exprs2)) => {
                let bty = self.join_bty(genv, bty1, bty2);
                let exprs = izip!(exprs1, exprs2, genv.sorts(&bty))
                    .map(|(e1, e2, sort)| {
                        let e2_has_free_vars = !self.scope.contains_all(e2.vars());
                        if !self.is_packed_expr(e1) && (e2_has_free_vars || e1 != e2) {
                            Expr::fvar(self.fresh(sort))
                        } else {
                            e1.clone()
                        }
                    })
                    .collect_vec();
                Ty::indexed(bty, exprs)
            }
            (TyKind::Exists(bty1, _), TyKind::Indexed(bty2, ..) | TyKind::Exists(bty2, ..))
            | (TyKind::Indexed(bty1, _), TyKind::Exists(bty2, ..)) => {
                let bty = self.join_bty(genv, bty1, bty2);
                Ty::exists(bty, Pred::Hole)
            }
            (TyKind::Ref(mode1, ty1), TyKind::Ref(mode2, ty2)) => {
                debug_assert_eq!(mode1, mode2);
                Ty::mk_ref(*mode1, self.join_ty(genv, ty1, ty2))
            }
            (TyKind::Float(float_ty1), TyKind::Float(float_ty2)) => {
                debug_assert_eq!(float_ty1, float_ty2);
                Ty::float(*float_ty1)
            }
            (TyKind::Param(param_ty1), TyKind::Param(param_ty2)) => {
                debug_assert_eq!(param_ty1, param_ty2);
                Ty::param(*param_ty1)
            }
            (TyKind::Tuple(tys1), TyKind::Tuple(tys2)) => {
                assert!(
                    tys1.is_empty() && tys2.is_empty(),
                    "join of non-empty tuples is not supported yet"
                );
                Ty::tuple(vec![])
            }
            _ => todo!("`{ty1:?}` -- `{ty2:?}`"),
        }
    }

    fn join_bty(&mut self, genv: &GlobalEnv, bty1: &BaseTy, bty2: &BaseTy) -> BaseTy {
        if let (BaseTy::Adt(def1, substs1), BaseTy::Adt(def2, substs2)) = (bty1, bty2) {
            debug_assert_eq!(def1.def_id(), def2.def_id());
            let variances = genv.variances_of(def1.def_id());
            let substs = izip!(variances, substs1, substs2).map(|(variance, ty1, ty2)| {
                assert!(matches!(variance, rustc_middle::ty::Variance::Covariant));
                self.join_ty(genv, ty1, ty2)
            });
            BaseTy::adt(def1.clone(), substs)
        } else {
            debug_assert_eq!(bty1, bty2);
            bty1.clone()
        }
    }

    fn fresh(&mut self, sort: Sort) -> Name {
        let fresh = self.name_gen.fresh();
        self.params.insert(fresh, sort);
        fresh
    }

    pub fn into_bb_env(
        self,
        genv: &GlobalEnv,
        fresh_kvar: &mut impl FnMut(&[Sort], &[Param]) -> Pred,
    ) -> BasicBlockEnv {
        let mut params = vec![];
        let mut constrs = vec![];
        // HACK(nilehmann) it is crucial that the order in this iteration is the same as
        // [`TypeEnvInfer::enter`] otherwise names will be out of order in the checking phase.
        for (name, sort) in self.params {
            if sort != Sort::loc() {
                constrs.push(fresh_kvar(&[sort.clone()], &params));
            } else {
                constrs.push(Pred::tt())
            }
            params.push(Param { name, sort });
        }

        let fresh_kvar = &mut |bty: &BaseTy| fresh_kvar(&genv.sorts(bty), &params);

        let mut bindings = self.env.bindings;
        for ty in bindings.values_mut() {
            *ty = ty.fill_holes(fresh_kvar);
        }

        BasicBlockEnv { params, constrs, env: TypeEnv { bindings }, scope: self.scope }
    }

    fn is_packed_expr(&self, expr: &Expr) -> bool {
        matches!(expr.kind(), ExprKind::FreeVar(name) if self.params.contains_key(name))
    }

    fn packed_loc(&self, loc: Loc) -> Option<Name> {
        match loc {
            Loc::Free(name) if self.params.contains_key(&name) => Some(name),
            _ => None,
        }
    }
}

impl BasicBlockEnv {
    pub fn enter(&self, pcx: &mut PureCtxt) -> TypeEnv {
        let mut subst = Subst::empty();
        for (param, constr) in self.params.iter().zip(&self.constrs) {
            let e = pcx.push_binding(param.sort.clone(), &subst.subst_pred(constr));
            subst.insert(param.name, e);
        }
        self.env.clone().subst(&subst)
    }
}

mod pretty {
    use super::*;
    use itertools::Itertools;
    use liquid_rust_middle::pretty::*;
    use std::fmt;

    impl Pretty for TypeEnv {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            let bindings = self
                .bindings
                .iter()
                .filter(|(_, ty)| !cx.hide_uninit || !ty.is_uninit())
                .collect_vec();

            w!(
                "{{{}}}",
                ^bindings
                    .into_iter()
                    .format_with(", ", |(loc, ty), f| f(&format_args_cx!("{:?}: {:?}", loc, ty)))
            )
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).kvar_args(Visibility::Hide)
        }
    }

    impl Pretty for TypeEnvInfer {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!(
                "{:?} ∃ {}. {:?}",
                &self.scope,
                ^self.params
                    .iter()
                    .format_with(", ", |(name, sort), f| f(&format_args_cx!("{:?}: {:?}", ^name, ^sort))),
                &self.env
            )
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).kvar_args(Visibility::Hide)
        }
    }

    impl Pretty for BasicBlockEnv {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!(
                "∃ {}. {:?}",
                ^self.params
                    .iter()
                    .zip(&self.constrs)
                    .format_with(", ", |(param, constr), f| {
                        if constr.is_true() {
                            f(&format_args_cx!("{:?}: {:?}", ^param.name, ^param.sort))
                        } else {
                            f(&format_args_cx!("{:?}: {:?}{{{:?}}}", ^param.name, ^param.sort, constr))
                        }
                    }),
                &self.env
            )
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).kvar_args(Visibility::Hide)
        }
    }

    impl_debug_with_default_cx!(TypeEnv => "type_env", TypeEnvInfer => "type_env_infer", BasicBlockEnv => "basic_block_env");
}
