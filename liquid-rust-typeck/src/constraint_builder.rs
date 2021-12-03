use std::{
    fmt::{self, Write},
    marker::PhantomData,
    ptr::NonNull,
};

use crate::ty::{self, BaseTy, Expr, ExprKind, Pred, Sort, Ty, TyKind, Var};
use fixpoint::{BinOp, KVar, KVid, Name};
use itertools::{izip, Itertools};
use liquid_rust_common::{
    format::PadAdapter,
    index::{IndexGen, IndexVec},
};
use liquid_rust_fixpoint as fixpoint;
use rustc_middle::ty::TyCtxt;

pub struct ConstraintBuilder<'tcx> {
    tcx: TyCtxt<'tcx>,
    root: Node,
    kvars: IndexVec<KVid, Vec<Sort>>,
    scopes: Vec<usize>,
    vars: Vec<(Name, Sort)>,
    name_gen: IndexGen<Name>,
}

pub struct Cursor<'a, 'tcx> {
    builder: &'a mut ConstraintBuilder<'tcx>,
    node: NonNull<Node>,
    nscopes: usize,
    nvars: usize,
}

enum Node {
    Conj(Vec<Node>),
    ForAll(Name, Sort, Pred, Vec<Node>),
    Guard(Expr, Vec<Node>),
    Head(Pred),
}

impl<'tcx> ConstraintBuilder<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            root: Node::Conj(vec![]),
            kvars: IndexVec::new(),
            scopes: vec![],
            vars: vec![],
            name_gen: IndexGen::new(),
        }
    }

    pub fn as_cursor<'a>(&'a mut self) -> Cursor<'a, 'tcx> {
        unsafe {
            Cursor {
                node: NonNull::new_unchecked(&mut self.root as *mut Node),
                builder: self,
                nvars: 0,
                nscopes: 0,
            }
        }
    }

    pub fn to_fixpoint(self) -> fixpoint::Fixpoint {
        let constraint = self
            .root
            .to_fixpoint(&self.name_gen, &self.kvars)
            .unwrap_or(fixpoint::Constraint::TRUE);
        let kvars = self
            .kvars
            .into_iter_enumerated()
            .map(|(kvid, sorts)| KVar(kvid, sorts))
            .collect();
        fixpoint::Fixpoint::new(kvars, constraint)
    }
}

impl<'tcx> Cursor<'_, 'tcx> {
    pub fn snapshot<'a>(&'a mut self) -> Cursor<'a, 'tcx> {
        Cursor {
            builder: &mut self.builder,
            ..*self
        }
    }

    pub fn push_scope(&mut self) {
        if self.nscopes < self.builder.scopes.len() {
            self.builder.scopes[self.nscopes] = self.nvars;
        } else {
            self.builder.scopes.push(self.nvars);
        }
        self.nscopes += 1;
    }

    pub fn push_forall(&mut self, var: Name, sort: Sort, pred: impl Into<Pred>) {
        self.push_node(Node::ForAll(var, sort, pred.into(), vec![]));
        self.push_var(var, sort);
    }

    pub fn push_guard(&mut self, expr: Expr) {
        self.push_node(Node::Guard(expr, vec![]));
    }

    pub fn push_head(&mut self, pred: impl Into<Pred>) {
        let pred = pred.into();
        if !pred.is_true() {
            self.push_node(Node::Head(pred));
        }
    }

    pub fn fresh_kvar(&mut self, sort: Sort) -> Pred {
        self.fresh_kvar_at_scope(sort, self.nvars)
    }

    pub fn fresh_kvar_at_last_scope(&mut self, sort: Sort) -> Pred {
        let scope = self.builder.scopes.last().copied().unwrap_or(0);
        self.fresh_kvar_at_scope(sort, scope)
    }

    fn fresh_kvar_at_scope(&mut self, sort: Sort, scope: usize) -> Pred {
        let mut sorts = Vec::with_capacity(self.nvars + 1);
        let mut vars = Vec::with_capacity(self.nvars);

        sorts.push(sort);
        for (var, sort) in self.vars_in_scope(scope) {
            vars.push(Expr::from(Var::Free(var)));
            sorts.push(sort);
        }

        let kvid = self.builder.kvars.push(sorts);
        Pred::kvar(kvid, Expr::from(Var::Bound), vars)
    }

    pub fn fresh_name(&self) -> Name {
        self.builder.name_gen.fresh()
    }

    pub fn subtyping(&mut self, ty1: Ty, ty2: Ty) {
        let mut cursor = self.snapshot();

        // Optimize trivially satisfiable constraints
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Refine(bty1, e1), TyKind::Refine(bty2, e2)) if e1 == e2 => {
                cursor.bty_subtyping(bty1, bty2);
                return;
            }
            (TyKind::Exists(bty1, p1), TyKind::Exists(bty2, p2)) if p1 == p2 => {
                cursor.bty_subtyping(bty1, bty2);
                return;
            }
            _ => {}
        }

        let ty1 = cursor.unpack(ty1);
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Refine(bty1, e1), TyKind::Refine(bty2, e2)) => {
                cursor.bty_subtyping(bty1, bty2);
                cursor.push_head(ExprKind::BinaryOp(BinOp::Eq, e1.clone(), e2.clone()).intern());
            }
            (TyKind::Refine(bty1, e), TyKind::Exists(bty2, p)) => {
                cursor.bty_subtyping(bty1, bty2);
                let p = p.subst_bound_vars(e.clone());
                cursor.push_head(p.subst_bound_vars(e.clone()))
            }
            (TyKind::MutRef(r1), TyKind::MutRef(r2)) => {
                assert!(r1.subset(r2));
            }
            (_, TyKind::Uninit) => {
                // FIXME: we should rethink in which situation this is sound.
            }
            (TyKind::Param(param1), TyKind::Param(param2)) => {
                debug_assert_eq!(param1, param2)
            }
            (TyKind::Exists(..), _) => {
                unreachable!("subtyping with unpacked existential")
            }
            _ => {
                unreachable!("unexpected types: `{:?}` `{:?}`", ty1, ty2)
            }
        }
    }

    fn bty_subtyping(&mut self, bty1: &BaseTy, bty2: &BaseTy) {
        match (bty1, bty2) {
            (BaseTy::Int(int_ty1), BaseTy::Int(int_ty2)) => {
                debug_assert_eq!(int_ty1, int_ty2);
            }
            (BaseTy::Uint(uint_ty1), BaseTy::Uint(uint_ty2)) => {
                debug_assert_eq!(uint_ty1, uint_ty2);
            }
            (BaseTy::Bool, BaseTy::Bool) => {}
            (BaseTy::Adt(did1, substs1), BaseTy::Adt(did2, substs2)) => {
                debug_assert_eq!(did1, did2);
                debug_assert_eq!(substs1.len(), substs2.len());
                let variances = self.builder.tcx.variances_of(*did1);
                for (variance, ty1, ty2) in izip!(variances, substs1.iter(), substs2.iter()) {
                    self.polymorphic_subtyping(*variance, ty1.clone(), ty2.clone());
                }
            }
            _ => unreachable!("unexpected base types: `{:?}` `{:?}`", bty1, bty2),
        }
    }

    fn polymorphic_subtyping(&mut self, variance: rustc_middle::ty::Variance, ty1: Ty, ty2: Ty) {
        match variance {
            rustc_middle::ty::Variance::Covariant => {
                self.subtyping(ty1, ty2);
            }
            rustc_middle::ty::Variance::Invariant => {
                self.subtyping(ty1.clone(), ty2.clone());
                self.subtyping(ty2, ty1);
            }
            rustc_middle::ty::Variance::Contravariant => {
                self.subtyping(ty2, ty1);
            }
            rustc_middle::ty::Variance::Bivariant => {}
        }
    }

    pub fn unpack(&mut self, ty: Ty) -> Ty {
        match ty.kind() {
            TyKind::Exists(bty, p) => {
                let fresh = self.fresh_name();
                self.push_forall(
                    fresh,
                    bty.sort(),
                    p.subst_bound_vars(ExprKind::Var(Var::Free(fresh)).intern()),
                );
                TyKind::Refine(bty.clone(), ExprKind::Var(Var::Free(fresh)).intern()).intern()
            }
            _ => ty,
        }
    }

    fn push_node(&mut self, node: Node) {
        unsafe {
            let children = match self.node.as_mut() {
                Node::Conj(children)
                | Node::ForAll(_, _, _, children)
                | Node::Guard(_, children) => children,
                Node::Head(_) => unreachable!("trying to push into a head node."),
            };
            children.push(node);
            let node = children.last_mut().unwrap();
            if !node.is_head() {
                self.node = NonNull::new_unchecked(node as *mut Node);
            }
        }
    }

    fn push_var(&mut self, var: Name, sort: Sort) {
        if self.nvars < self.builder.vars.len() {
            self.builder.vars[self.nvars] = (var, sort);
        } else {
            self.builder.vars.push((var, sort));
        }
        self.nvars += 1;
    }

    fn vars_in_scope(&self, scope: usize) -> impl Iterator<Item = (Name, Sort)> + '_ {
        self.builder.vars[..scope].iter().cloned()
    }
}

impl Node {
    fn to_fixpoint(
        self,
        name_gen: &IndexGen<Name>,
        kvars: &IndexVec<KVid, Vec<Sort>>,
    ) -> Option<fixpoint::Constraint> {
        match self {
            Node::Conj(children) => children_to_fixpoint(name_gen, kvars, children),
            Node::ForAll(var, sort, pred, children) => {
                let (bindings, pred) = pred_to_fixpoint(name_gen, kvars, pred);
                Some(stitch(
                    bindings,
                    fixpoint::Constraint::ForAll(
                        var,
                        sort,
                        pred,
                        Box::new(children_to_fixpoint(name_gen, kvars, children)?),
                    ),
                ))
            }
            Node::Guard(expr, children) => Some(fixpoint::Constraint::Guard(
                expr_to_fixpoint(expr),
                Box::new(children_to_fixpoint(name_gen, kvars, children)?),
            )),
            Node::Head(pred) => {
                let (bindings, pred) = pred_to_fixpoint(name_gen, kvars, pred);
                Some(stitch(bindings, fixpoint::Constraint::Pred(pred)))
            }
        }
    }

    /// Returns `true` if the node is [`Head`].
    ///
    /// [`Head`]: Node::Head
    fn is_head(&self) -> bool {
        matches!(self, Self::Head(..))
    }

    fn forall_chain<'a>(&'a self) -> Option<(Vec<(Name, Sort, &'a Pred)>, &'a Vec<Node>)> {
        fn go<'a>(
            node: &'a Node,
            mut vec: Vec<(Name, Sort, &'a Pred)>,
        ) -> Option<(Vec<(Name, Sort, &'a Pred)>, &'a Vec<Node>)> {
            match node {
                Node::ForAll(name, sort, pred, children) => {
                    vec.push((*name, *sort, pred));
                    match &children[..] {
                        [child @ Node::ForAll(..)] => go(child, vec),
                        _ => Some((vec, children)),
                    }
                }
                _ => None,
            }
        }
        go(self, vec![])
    }
}

fn children_to_fixpoint(
    name_gen: &IndexGen<Name>,
    kvars: &IndexVec<KVid, Vec<Sort>>,
    children: Vec<Node>,
) -> Option<fixpoint::Constraint> {
    let mut children = children
        .into_iter()
        .filter_map(|node| node.to_fixpoint(name_gen, kvars))
        .collect_vec();
    match children.len() {
        0 => None,
        1 => children.pop(),
        _ => Some(fixpoint::Constraint::Conj(children)),
    }
}

fn pred_to_fixpoint(
    name_gen: &IndexGen<Name>,
    kvars: &IndexVec<KVid, Vec<Sort>>,
    refine: Pred,
) -> (Vec<(Name, Sort, fixpoint::Expr)>, fixpoint::Pred) {
    let mut bindings = vec![];
    let pred = match refine {
        Pred::Expr(expr) => fixpoint::Pred::Expr(expr_to_fixpoint(expr)),
        Pred::KVar(kvid, e, args) => {
            let args = std::iter::once(&e)
                .chain(args.iter())
                .zip(&kvars[kvid])
                .map(|(arg, sort)| {
                    if let ExprKind::Var(Var::Free(var)) = arg.kind() {
                        *var
                    } else {
                        let fresh = name_gen.fresh();
                        let pred = fixpoint::Expr::BinaryOp(
                            BinOp::Eq,
                            Box::new(fixpoint::Expr::Var(fresh)),
                            Box::new(expr_to_fixpoint(arg.clone())),
                        );
                        bindings.push((fresh, *sort, pred));
                        fresh
                    }
                });
            fixpoint::Pred::KVar(kvid, args.collect())
        }
    };
    (bindings, pred)
}

fn expr_to_fixpoint(expr: ty::Expr) -> fixpoint::Expr {
    match expr.kind() {
        ty::ExprKind::Var(Var::Free(var)) => fixpoint::Expr::Var(*var),
        ty::ExprKind::Constant(c) => fixpoint::Expr::Constant(*c),
        ty::ExprKind::BinaryOp(op, e1, e2) => fixpoint::Expr::BinaryOp(
            *op,
            Box::new(expr_to_fixpoint(e1.clone())),
            Box::new(expr_to_fixpoint(e2.clone())),
        ),
        ty::ExprKind::UnaryOp(op, e) => {
            fixpoint::Expr::UnaryOp(*op, Box::new(expr_to_fixpoint(e.clone())))
        }
        ty::ExprKind::Var(Var::Bound) => {
            unreachable!("unexpected bound variable")
        }
    }
}

fn stitch(
    bindings: Vec<(Name, Sort, fixpoint::Expr)>,
    c: fixpoint::Constraint,
) -> fixpoint::Constraint {
    bindings.into_iter().rev().fold(c, |c, (var, sort, e)| {
        fixpoint::Constraint::ForAll(var, sort, fixpoint::Pred::Expr(e), Box::new(c))
    })
}

mod pretty {
    use super::*;
    use crate::pretty::*;

    impl Pretty for ConstraintBuilder<'_> {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            w!("{:?}", &self.root)
        }

        fn default_cx(tcx: TyCtxt) -> PPrintCx {
            PPrintCx::default(tcx).vars_in_scope(Visibility::Ellipsis)
        }
    }

    impl Pretty for Node {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, f);
            match &self {
                Node::Conj(children) => {
                    w!("{:?}", join!("\n", children))
                }
                Node::ForAll(..) => {
                    let (bindings, children) = self.forall_chain().unwrap();

                    let vars = bindings.iter().format_with(", ", |(var, sort, _), f| {
                        f(&format_args_cx!("{:?}: {:?}", ^var, ^sort))
                    });

                    let preds = bindings
                        .iter()
                        .map(|(_, _, pred)| pred)
                        .filter(|p| !p.is_true())
                        .collect_vec();

                    let preds_fmt = preds.iter().format_with(" ∧ ", |pred, f| {
                        if pred.is_atom() {
                            f(&format_args_cx!("{:?}", pred))
                        } else {
                            f(&format_args_cx!("({:?})", pred))
                        }
                    });

                    w!("∀ {}.", ^vars)?;
                    if preds.is_empty() {
                        w!("{:?}", children)
                    } else {
                        w!(PadAdapter::wrap_fmt(f), "\n{} ⇒{:?}", ^preds_fmt, children)
                    }
                }
                Node::Guard(expr, children) => {
                    if expr.is_atom() {
                        w!("{:?} ⇒{:?}", expr, children)
                    } else {
                        w!("({:?}) ⇒{:?}", expr, children)
                    }
                }
                Node::Head(pred) => {
                    if pred.is_atom() {
                        w!("{:?}", pred)
                    } else {
                        w!("({:?})", pred)
                    }
                }
            }
        }
    }

    impl Pretty for Vec<Node> {
        fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            define_scoped!(cx, PadAdapter::wrap_fmt(f));
            match &self[..] {
                [] => w!(" true"),
                [n] => w!(" {:?}", n),
                _ => w!("\n{:?}", join!("\n", self)),
            }
        }
    }

    // fn debug_children(children: &[Node], f: &mut fmt::Formatter<'_>) -> fmt::Result {
    //     let mut w = PadAdapter::wrap_fmt(f);
    //     for child in children {
    //         write!(w, "\n{:?}", child)?;
    //     }
    //     if children.is_empty() {
    //         write!(f, " ")
    //     } else {
    //         writeln!(f)
    //     }
    // }

    impl fmt::Debug for Cursor<'_, '_> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                f,
                "{{{}}}",
                self.vars_in_scope(self.nvars)
                    .format_with(", ", |(var, sort), f| f(&format_args!(
                        "{:?}: {:?}",
                        var, sort
                    )))
            )
        }
    }

    impl_debug_with_default_cx!(ConstraintBuilder<'_>, Node);
}
