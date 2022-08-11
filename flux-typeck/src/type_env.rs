pub mod paths_tree;

use std::{iter, slice};

use flux_common::index::IndexGen;
use itertools::{izip, Itertools};

use rustc_hash::FxHashSet;
use rustc_middle::ty::TyCtxt;

use flux_middle::{
    global_env::GlobalEnv,
    rustc::mir::Place,
    ty::{
        fold::TypeFoldable, subst::FVarSubst, BaseTy, Binders, Expr, Index, Path, RefKind, Ty,
        TyKind,
    },
};

use crate::{
    constraint_gen::ConstrGen,
    fixpoint::KVarGen,
    param_infer,
    refine_tree::{RefineCtxt, Scope},
};

use self::paths_tree::{Binding, LookupResult, PathsTree};

use super::ty::{Loc, Name, Pred, Sort};

pub trait PathMap {
    fn get(&self, path: &Path) -> Ty;
    fn update(&mut self, path: &Path, ty: Ty);
}

#[derive(Clone, Default)]
pub struct TypeEnv {
    bindings: PathsTree,
}

pub struct TypeEnvInfer {
    scope: Scope,
    bindings: PathsTree,
}

pub struct BasicBlockEnv {
    params: Vec<(Name, Sort)>,
    constrs: Vec<Binders<Pred>>,
    scope: Scope,
    bindings: PathsTree,
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

    #[track_caller]
    pub fn lookup_place(&mut self, rcx: &mut RefineCtxt, gen: &mut ConstrGen, place: &Place) -> Ty {
        self.bindings.lookup_place(rcx, gen, place).ty()
    }

    pub fn update_path(&mut self, path: &Path, new_ty: Ty) {
        self.bindings.update(path, new_ty);
    }

    // TODO(nilehmann) find a better name for borrow in this context
    // TODO(nilehmann) unify borrow_mut and borrow_shr and return ptr(l)
    pub fn borrow_mut(&mut self, rcx: &mut RefineCtxt, gen: &mut ConstrGen, place: &Place) -> Ty {
        match self.bindings.lookup_place(rcx, gen, place) {
            LookupResult::Ptr(path, _) => Ty::ptr(path),
            LookupResult::Ref(RefKind::Mut, ty) => Ty::mk_ref(RefKind::Mut, ty),
            LookupResult::Ref(RefKind::Shr, _) => {
                panic!("cannot borrow `{place:?}` as mutable, as it is behind a `&`")
            }
        }
    }

    pub fn borrow_shr(&mut self, rcx: &mut RefineCtxt, gen: &mut ConstrGen, place: &Place) -> Ty {
        match self.bindings.lookup_place(rcx, gen, place) {
            LookupResult::Ptr(path, ty) => {
                self.bindings.block(&path);
                Ty::mk_ref(RefKind::Shr, ty)
            }
            result => Ty::mk_ref(RefKind::Shr, result.ty()),
        }
    }

    pub fn write_place(
        &mut self,
        rcx: &mut RefineCtxt,
        gen: &mut ConstrGen,
        place: &Place,
        new_ty: Ty,
    ) {
        match self.bindings.lookup_place(rcx, gen, place) {
            LookupResult::Ptr(path, _) => {
                self.bindings.update(&path, new_ty);
            }
            LookupResult::Ref(RefKind::Mut, ty) => {
                gen.subtyping(rcx, &new_ty, &ty);
            }
            LookupResult::Ref(RefKind::Shr, _) => {
                panic!("cannot assign to `{place:?}`, which is behind a `&` reference or Box")
            }
        }
    }

    pub fn move_place(&mut self, rcx: &mut RefineCtxt, gen: &mut ConstrGen, place: &Place) -> Ty {
        match self.bindings.lookup_place(rcx, gen, place) {
            LookupResult::Ptr(path, ty) => {
                self.bindings.update(&path, Ty::uninit());
                ty
            }
            LookupResult::Ref(RefKind::Mut, _) => {
                panic!("cannot move out of `{place:?}`, which is behind a `&mut` reference")
            }
            LookupResult::Ref(RefKind::Shr, _) => {
                panic!("cannot move out of `{place:?}`, which is behind a `&` reference")
            }
        }
    }

    pub fn close_boxes(&mut self, genv: &GlobalEnv, scope: &Scope) {
        let mut to_remove = vec![];
        for path in self.bindings.paths() {
            if let Binding::Owned(ty) = self.bindings.get(&path) &&
               let TyKind::BoxPtr(loc, alloc) = ty.kind() &&
               !scope.contains(*loc) {
                let loc = Loc::Free(*loc);
                to_remove.push(loc);
                let ty = self.bindings.get(&Path::from(loc)).expect_owned();
                self.bindings.update(&path, genv.mk_box(ty, alloc.clone()))
            }
        }
        for loc in to_remove {
            self.bindings.remove(loc);
        }
    }

    pub fn unpack(&mut self, rcx: &mut RefineCtxt) {
        self.bindings.fmap_mut(|binding| {
            match binding {
                Binding::Owned(ty) => Binding::Owned(rcx.unpack(ty, false)),
                Binding::Blocked(ty) => Binding::Blocked(ty.clone()),
            }
        });
    }

    fn infer_subst_for_bb_env(&self, bb_env: &BasicBlockEnv) -> FVarSubst {
        let params = bb_env.params.iter().map(|(name, _)| *name).collect();
        let mut subst = FVarSubst::empty();
        self.bindings.iter(|path, binding1| {
            let binding2 = bb_env.bindings.get(&path);
            if bb_env.bindings.contains_loc(path.loc)
              && let Binding::Owned(ty1) = binding1
              && let Binding::Owned(ty2) = binding2 {
                self.infer_subst_for_bb_env_ty(bb_env, &params, ty1, &ty2, &mut subst);
            }
        });

        param_infer::check_inference(
            &subst,
            bb_env
                .params
                .iter()
                .filter(|(_, sort)| !sort.is_loc())
                .map(|(name, _)| *name),
        )
        .unwrap();
        subst
    }

    fn infer_subst_for_bb_env_ty(
        &self,
        bb_env: &BasicBlockEnv,
        params: &FxHashSet<Name>,
        ty1: &Ty,
        ty2: &Ty,
        subst: &mut FVarSubst,
    ) {
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Indexed(bty1, indices1), TyKind::Indexed(bty2, indices2)) => {
                self.infer_subst_for_bb_env_bty(bb_env, params, bty1, bty2, subst);
                for (idx1, idx2) in iter::zip(indices1, indices2) {
                    subst.infer_from_exprs(params, &idx1.expr, &idx2.expr);
                }
            }
            (TyKind::Ptr(path1), TyKind::Ptr(path2)) => {
                subst.infer_from_exprs(params, &path1.to_expr(), &path2.to_expr());
                if let Binding::Owned(ty1) = self.bindings.get(path1) &&
                   let Binding::Owned(ty2) = bb_env.bindings.get(path2) {
                    self.infer_subst_for_bb_env_ty(bb_env, params, &ty1, &ty2, subst);
                }
            }
            (TyKind::Ref(mode1, ty1), TyKind::Ref(mode2, ty2)) => {
                debug_assert_eq!(mode1, mode2);
                self.infer_subst_for_bb_env_ty(bb_env, params, ty1, ty2, subst);
            }
            _ => {}
        }
    }

    fn infer_subst_for_bb_env_bty(
        &self,
        bb_env: &BasicBlockEnv,
        params: &FxHashSet<Name>,
        bty1: &BaseTy,
        bty2: &BaseTy,
        subst: &mut FVarSubst,
    ) {
        if bty1.is_box()  &&
           let BaseTy::Adt(_, substs1) = bty1 &&
           let BaseTy::Adt(_, substs2) = bty2 {
            for (ty1, ty2) in iter::zip(substs1, substs2) {
                self.infer_subst_for_bb_env_ty(bb_env, params, ty1, ty2, subst);
            }
        }
    }

    pub fn check_goto(mut self, rcx: &mut RefineCtxt, gen: &mut ConstrGen, bb_env: &BasicBlockEnv) {
        self.close_boxes(gen.genv, &bb_env.scope);

        // Look up path to make sure they are properly folded/unfolded
        for path in bb_env.bindings.paths() {
            self.bindings.lookup_path(rcx, gen, &path);
        }

        // Infer subst
        let subst = self.infer_subst_for_bb_env(bb_env);

        // Check constraints
        for ((name, _), constr) in iter::zip(&bb_env.params, &bb_env.constrs) {
            gen.check_pred(rcx, subst.apply(&constr.replace_bound_vars(&[Expr::fvar(*name)])));
        }

        let bb_env = bb_env
            .bindings
            .fmap(|binding| subst.apply(binding))
            .flatten();

        // Convert pointers to borrows
        for (path, binding2) in &bb_env {
            let binding1 = self.bindings.get(path);
            if let (Binding::Owned(ty1), Binding::Owned(ty2)) = (binding1, binding2) &&
               let (TyKind::Ptr(ptr_path), TyKind::Ref(RefKind::Mut, bound)) = (ty1.kind(), ty2.kind())
            {

                let ty = self.bindings.get(ptr_path).expect_owned();
                gen.subtyping(rcx, &ty, bound);

                self.bindings.update_binding(ptr_path, Binding::Blocked(bound.clone()));
                self.bindings.update(path, Ty::mk_ref(RefKind::Mut, bound.clone()));
            }
        }

        // Check subtyping
        for (path, binding2) in bb_env {
            let binding1 = self.bindings.get(&path);
            let ty1 = binding1.ty();
            let ty2 = binding2.ty();
            gen.subtyping(rcx, ty1, ty2);
        }
    }
}

impl PathMap for TypeEnv {
    fn get(&self, path: &Path) -> Ty {
        self.bindings.get(path).expect_owned()
    }

    fn update(&mut self, path: &Path, ty: Ty) {
        self.bindings.update(path, ty)
    }
}

impl<S> PathMap for std::collections::HashMap<Path, Ty, S>
where
    S: std::hash::BuildHasher,
{
    fn get(&self, path: &Path) -> Ty {
        self.get(path).unwrap().clone()
    }

    fn update(&mut self, path: &Path, ty: Ty) {
        self.insert(path.clone(), ty);
    }
}

impl TypeEnvInfer {
    pub fn enter(&self) -> TypeEnv {
        TypeEnv { bindings: self.bindings.clone() }
    }

    fn new(genv: &GlobalEnv, scope: Scope, mut env: TypeEnv) -> TypeEnvInfer {
        env.close_boxes(genv, &scope);
        let mut bindings = env.bindings;
        bindings.fmap_mut(|binding| {
            match binding {
                Binding::Owned(ty) => Binding::Owned(TypeEnvInfer::pack_ty(&scope, ty)),
                Binding::Blocked(ty) => Binding::Blocked(TypeEnvInfer::pack_ty(&scope, ty)),
            }
        });
        TypeEnvInfer { bindings, scope }
    }

    fn pack_ty(scope: &Scope, ty: &Ty) -> Ty {
        match ty.kind() {
            TyKind::Indexed(bty, idxs) => {
                let bty = TypeEnvInfer::pack_bty(scope, bty);
                if scope.has_free_vars(idxs) {
                    let pred = Binders::new(Pred::Hole, bty.sorts());
                    Ty::exists(bty, pred)
                } else {
                    Ty::indexed(bty, idxs.clone())
                }
            }
            TyKind::Tuple(tys) => {
                let tys = tys
                    .iter()
                    .map(|ty| TypeEnvInfer::pack_ty(scope, ty))
                    .collect_vec();
                Ty::tuple(tys)
            }
            // TODO(nilehmann) [`TyKind::Exists`] could also in theory contains free variables.
            TyKind::Exists(_, _)
            | TyKind::Never
            | TyKind::Discr(..)
            | TyKind::Float(_)
            | TyKind::Ptr(_)
            | TyKind::Uninit
            | TyKind::Ref(..)
            | TyKind::Param(_)
            | TyKind::Constr(_, _)
            | TyKind::BoxPtr(_, _) => ty.clone(),
        }
    }

    fn pack_bty(scope: &Scope, bty: &BaseTy) -> BaseTy {
        match bty {
            BaseTy::Adt(adt_def, substs) => {
                let substs = substs.iter().map(|ty| Self::pack_ty(scope, ty));
                BaseTy::adt(adt_def.clone(), substs)
            }
            BaseTy::Int(_) | BaseTy::Uint(_) | BaseTy::Bool => bty.clone(),
        }
    }

    /// join(self, genv, other) consumes the bindings in other, to "update"
    /// `self` in place, and returns `true` if there was an actual change
    /// or `false` indicating no change (i.e., a fixpoint was reached).
    pub fn join(&mut self, rcx: &mut RefineCtxt, gen: &mut ConstrGen, mut other: TypeEnv) -> bool {
        other.close_boxes(gen.genv, &self.scope);

        // Unfold
        self.bindings.join_with(rcx, gen, &mut other.bindings);

        let paths = self.bindings.paths();

        // Convert pointers to borrows
        for path in &paths {
            let binding1 = self.bindings.get(path);
            let binding2 = other.bindings.get(path);
            if let (Binding::Owned(ty1), Binding::Owned(ty2)) = (binding1, binding2) {
                match (ty1.kind(), ty2.kind()) {
                    (TyKind::Ptr(path1), TyKind::Ptr(path2)) if path1 != path2 => {
                        let ty1 = self.bindings.get(path1).expect_owned().with_holes();
                        let ty2 = other.bindings.get(path2).expect_owned().with_holes();

                        self.bindings
                            .update(path, Ty::mk_ref(RefKind::Mut, ty1.clone()));
                        other
                            .bindings
                            .update(path, Ty::mk_ref(RefKind::Mut, ty2.clone()));

                        self.bindings.update_binding(path1, Binding::Blocked(ty1));
                        other.bindings.update_binding(path2, Binding::Blocked(ty2));
                    }
                    (TyKind::Ptr(ptr_path), TyKind::Ref(RefKind::Mut, bound)) => {
                        let bound = bound.with_holes();
                        self.bindings
                            .update_binding(ptr_path, Binding::Blocked(bound.clone()));
                        self.bindings.update(path, Ty::mk_ref(RefKind::Mut, bound));
                    }
                    (TyKind::Ref(RefKind::Mut, bound), TyKind::Ptr(ptr_path)) => {
                        let bound = bound.with_holes();
                        other
                            .bindings
                            .update_binding(ptr_path, Binding::Blocked(bound.clone()));
                        other.bindings.update(path, Ty::mk_ref(RefKind::Mut, bound));
                    }
                    _ => {}
                }
            }
        }

        // Join types
        let mut modified = false;
        for path in &paths {
            let binding1 = self.bindings.get(path);
            let binding2 = other.bindings.get(path);
            let binding = match (&binding1, &binding2) {
                (Binding::Owned(ty1), Binding::Owned(ty2)) => {
                    Binding::Owned(self.join_ty(gen.genv, ty1, ty2))
                }
                (Binding::Owned(ty1), Binding::Blocked(ty2)) => {
                    Binding::Blocked(self.join_ty(gen.genv, ty1, ty2))
                }
                (Binding::Blocked(ty1), Binding::Owned(ty2)) => {
                    Binding::Blocked(self.join_ty(gen.genv, ty1, ty2))
                }
                (Binding::Blocked(ty1), Binding::Blocked(ty2)) => {
                    Binding::Blocked(self.join_ty(gen.genv, ty1, ty2))
                }
            };
            modified |= binding1 != binding;
            self.bindings.update_binding(path, binding);
        }

        modified
    }

    fn join_ty(&self, genv: &GlobalEnv, ty1: &Ty, ty2: &Ty) -> Ty {
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Uninit, _) | (_, TyKind::Uninit) => Ty::uninit(),
            (TyKind::Ptr(path1), TyKind::Ptr(path2)) => {
                debug_assert_eq!(path1, path2);
                Ty::ptr(path1.clone())
            }
            (TyKind::BoxPtr(loc1, alloc1), TyKind::BoxPtr(loc2, alloc2)) => {
                debug_assert_eq!(loc1, loc2);
                debug_assert_eq!(alloc1, alloc2);
                Ty::box_ptr(*loc1, alloc1.clone())
            }
            (TyKind::Indexed(bty1, idxs1), TyKind::Indexed(bty2, idxs2)) => {
                let bty = self.join_bty(genv, bty1, bty2);
                if self.scope.has_free_vars(idxs2) || !Index::exprs_eq(idxs1, idxs2) {
                    let pred = Binders::new(Pred::Hole, bty.sorts());
                    Ty::exists(bty, pred)
                } else {
                    Ty::indexed(bty, idxs1.clone())
                }
            }
            (TyKind::Exists(bty1, _), TyKind::Indexed(bty2, ..) | TyKind::Exists(bty2, ..))
            | (TyKind::Indexed(bty1, _), TyKind::Exists(bty2, ..)) => {
                let bty = self.join_bty(genv, bty1, bty2);
                let pred = Binders::new(Pred::Hole, bty.sorts());
                Ty::exists(bty, pred)
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

    fn join_bty(&self, genv: &GlobalEnv, bty1: &BaseTy, bty2: &BaseTy) -> BaseTy {
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

    pub fn into_bb_env(self, kvar_gen: &mut impl KVarGen) -> BasicBlockEnv {
        let mut kvar_gen = kvar_gen.chaining(&self.scope);

        let mut params = vec![];
        let mut preds = vec![];
        let mut bindings = self.bindings;

        let name_gen = self.scope.name_gen();
        bindings.fmap_mut(|binding| {
            match binding {
                Binding::Owned(ty) => {
                    let ty = generalize(&name_gen, ty, &mut params, &mut preds);
                    Binding::Owned(ty)
                }
                Binding::Blocked(ty) => Binding::Blocked(ty.clone()),
            }
        });

        let mut scope = vec![];
        let constrs = iter::zip(&params, preds)
            .map(|((name, sort), pred)| {
                let constr = if let Pred::Hole = pred {
                    kvar_gen.fresh(slice::from_ref(sort), scope.iter().cloned())
                } else {
                    pred
                };
                scope.push((*name, sort.clone()));
                Binders::new(constr, vec![sort.clone()])
            })
            .collect_vec();

        let fresh_kvar = &mut |sorts: &[Sort]| kvar_gen.fresh(sorts, scope.iter().cloned());

        bindings.fmap_mut(|binding| binding.replace_holes(fresh_kvar));

        BasicBlockEnv { params, constrs, bindings, scope: self.scope }
    }
}

/// This is effectively doing the same than [`RefineCtxt::unpack`] but for moving existentials
/// to the top level in a [`BasicBlockEnv`]. Given the way we currently handle kvars it is tricky
/// to abstract over this in a way that can be used in both places.
fn generalize(
    name_gen: &IndexGen<Name>,
    ty: &Ty,
    params: &mut Vec<(Name, Sort)>,
    preds: &mut Vec<Pred>,
) -> Ty {
    match ty.kind() {
        TyKind::Indexed(bty, idxs) => {
            let bty = generalize_bty(name_gen, bty, params, preds);
            Ty::indexed(bty, idxs.clone())
        }
        TyKind::Exists(bty, pred) => {
            let bty = generalize_bty(name_gen, bty, params, preds);
            let mut idxs = vec![];
            for (name, sort, pred) in pred.split_with_fresh_fvars(name_gen) {
                params.push((name, sort));
                preds.push(pred);
                idxs.push(Expr::fvar(name).into())
            }
            Ty::indexed(bty, idxs)
        }
        TyKind::Ref(RefKind::Shr, ty) => {
            let ty = generalize(name_gen, ty, params, preds);
            Ty::mk_ref(RefKind::Shr, ty)
        }
        _ => ty.clone(),
    }
}

fn generalize_bty(
    name_gen: &IndexGen<Name>,
    bty: &BaseTy,
    params: &mut Vec<(Name, Sort)>,
    preds: &mut Vec<Pred>,
) -> BaseTy {
    match bty {
        BaseTy::Adt(adt_def, substs) if adt_def.is_box() => {
            let ty = generalize(name_gen, &substs[0], params, preds);
            BaseTy::adt(adt_def.clone(), vec![ty, substs[1].clone()])
        }
        _ => bty.clone(),
    }
}

impl BasicBlockEnv {
    pub fn enter(&self, rcx: &mut RefineCtxt) -> TypeEnv {
        let mut subst = FVarSubst::empty();
        for ((name, _), constr) in iter::zip(&self.params, &self.constrs) {
            let fresh = rcx.define_var_for_binder(&subst.apply(constr));
            subst.insert(*name, Expr::fvar(fresh));
        }
        let bindings = self.bindings.fmap(|binding| subst.apply(binding));
        TypeEnv { bindings }
    }

    pub fn scope(&self) -> &Scope {
        &self.scope
    }
}

mod pretty {
    use super::*;
    use flux_middle::pretty::*;
    use itertools::Itertools;
    use std::fmt;

    impl Pretty for TypeEnv {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("{:?}", &self.bindings)
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).kvar_args(Visibility::Hide)
        }
    }

    impl Pretty for TypeEnvInfer {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("{:?} {:?}", &self.scope, &self.bindings)
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).kvar_args(Visibility::Hide)
        }
    }

    impl Pretty for BasicBlockEnv {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!(
                "{:?} ∃ {}. {:?}",
                &self.scope,
                ^iter::zip(&self.params, &self.constrs)
                    .format_with(", ", |((name, sort), constr), f| {
                        if constr.is_true() {
                            f(&format_args_cx!("{:?}: {:?}", ^name, ^sort))
                        } else {
                            f(&format_args_cx!("{:?}: {:?}{{{:?}}}", ^name, ^sort, constr))
                        }
                    }),
                &self.bindings
            )
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).kvar_args(Visibility::Hide)
        }
    }

    impl_debug_with_default_cx!(TypeEnv => "type_env", TypeEnvInfer => "type_env_infer", BasicBlockEnv => "basic_block_env");
}
