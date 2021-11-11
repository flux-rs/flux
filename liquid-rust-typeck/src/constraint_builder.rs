use std::{
    fmt::{self, Write},
    marker::PhantomData,
    ptr::NonNull,
};

use crate::{
    subst::Subst,
    ty::{self, Expr, ExprKind, Pred, Sort, Ty, TyKind, Var},
};
use fixpoint::{BinOp, KVar, KVid};
use itertools::Itertools;
use liquid_rust_common::{
    format::PadAdapter,
    index::{IndexGen, IndexVec},
};
use liquid_rust_fixpoint as fixpoint;

pub struct ConstraintBuilder {
    root: Node,
    kvars: IndexVec<KVid, Vec<Sort>>,
    vars: Vec<(Var, Sort)>,
}

pub struct Cursor<'a> {
    builder: &'a mut ConstraintBuilder,
    node: NonNull<Node>,
    nvars: usize,
}

enum Node {
    Conj(Vec<Node>),
    ForAll(Var, Sort, Pred, Vec<Node>),
    Guard(Expr, Vec<Node>),
    Head(Pred),
}

impl ConstraintBuilder {
    pub fn new() -> Self {
        ConstraintBuilder {
            root: Node::Conj(vec![]),
            kvars: IndexVec::new(),
            vars: vec![],
        }
    }

    pub fn as_cursor(&mut self) -> Cursor {
        unsafe {
            Cursor {
                node: NonNull::new_unchecked(&mut self.root as *mut Node),
                builder: self,
                nvars: 0,
            }
        }
    }

    pub fn to_fixpoint(self, name_gen: &IndexGen<Var>) -> fixpoint::Fixpoint {
        let constraint = self
            .root
            .to_fixpoint(name_gen, &self.kvars)
            .unwrap_or(fixpoint::Constraint::TRUE);
        let kvars = self
            .kvars
            .into_iter_enumerated()
            .map(|(kvid, sorts)| KVar(kvid, sorts))
            .collect();
        fixpoint::Fixpoint::new(kvars, constraint)
    }
}

impl Cursor<'_> {
    pub fn snapshot(&mut self) -> Cursor {
        Cursor {
            node: self.node,
            builder: &mut self.builder,
            nvars: self.nvars,
        }
    }

    pub fn push_forall(&mut self, var: Var, sort: Sort, pred: impl Into<Pred>) {
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

    pub fn fresh_kvar(&mut self, nu: Var, sort: Sort) -> Pred {
        let mut sorts = Vec::with_capacity(self.nvars + 1);
        let mut vars = Vec::with_capacity(self.nvars + 1);

        vars.push(Expr::from(nu));
        sorts.push(sort);
        for (var, sort) in self.vars_in_scope() {
            vars.push(Expr::from(var));
            sorts.push(sort);
        }

        let kvid = self.builder.kvars.push(sorts);
        Pred::kvar(kvid, vars)
    }

    pub fn subtyping(&mut self, ty1: ty::Ty, ty2: ty::Ty) {
        match (ty1.kind(), ty2.kind()) {
            (TyKind::Refine(bty1, e1), TyKind::Refine(bty2, e2)) => {
                debug_assert_eq!(bty1, bty2);
                if e1 != e2 {
                    self.push_head(ExprKind::BinaryOp(BinOp::Eq, e1.clone(), e2.clone()).intern());
                }
            }
            (TyKind::Refine(bty1, e), TyKind::Exists(bty2, evar, p)) => {
                debug_assert_eq!(bty1, bty2);
                self.push_head(Subst::new([(*evar, e.clone())]).subst_pred(p.clone()))
            }
            (TyKind::MutRef(r1), TyKind::MutRef(r2)) => {
                assert!(r1.subset(r2));
            }
            (TyKind::Uninit, TyKind::Uninit) => {}
            (TyKind::MutRef(_), TyKind::Uninit) => {}
            (TyKind::Exists(..), _) => {
                unreachable!("subtyping with unpacked existential")
            }
            _ => {
                unreachable!("unexpected types: `{:?}` `{:?}`", ty1, ty2)
            }
        }
    }

    pub fn unpack(&mut self, name_gen: &IndexGen<Var>, ty: ty::Ty) -> ty::Ty {
        match ty.kind() {
            TyKind::Exists(bty, evar, p) => {
                let fresh = name_gen.fresh();
                self.push_forall(
                    fresh,
                    bty.sort(),
                    Subst::new([(*evar, ExprKind::Var(fresh).intern())]).subst_pred(p.clone()),
                );
                TyKind::Refine(*bty, ExprKind::Var(fresh).intern()).intern()
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

    fn push_var(&mut self, var: Var, sort: Sort) {
        if self.nvars < self.builder.vars.len() {
            self.builder.vars[self.nvars] = (var, sort);
        } else {
            self.builder.vars.push((var, sort));
        }
        self.nvars += 1;
    }

    fn vars_in_scope(&self) -> impl Iterator<Item = (Var, Sort)> + '_ {
        self.builder.vars[..self.nvars].iter().cloned()
    }
}

impl Node {
    fn to_fixpoint(
        self,
        name_gen: &IndexGen<Var>,
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
}

fn children_to_fixpoint(
    name_gen: &IndexGen<Var>,
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
    name_gen: &IndexGen<Var>,
    kvars: &IndexVec<KVid, Vec<Sort>>,
    refine: Pred,
) -> (Vec<(Var, Sort, fixpoint::Expr)>, fixpoint::Pred) {
    let mut bindings = vec![];
    let pred = match refine {
        Pred::Expr(expr) => fixpoint::Pred::Expr(expr_to_fixpoint(expr)),
        Pred::KVar(kvid, args) => {
            let args = args.iter().zip(&kvars[kvid]).map(|(arg, sort)| {
                if let ExprKind::Var(var) = arg.kind() {
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
        ty::ExprKind::Var(x) => fixpoint::Expr::Var(*x),
        ty::ExprKind::Constant(c) => fixpoint::Expr::Constant(*c),
        ty::ExprKind::BinaryOp(op, e1, e2) => fixpoint::Expr::BinaryOp(
            *op,
            Box::new(expr_to_fixpoint(e1.clone())),
            Box::new(expr_to_fixpoint(e2.clone())),
        ),
        ty::ExprKind::UnaryOp(op, e) => {
            fixpoint::Expr::UnaryOp(*op, Box::new(expr_to_fixpoint(e.clone())))
        }
    }
}

fn stitch(
    bindings: Vec<(Var, Sort, fixpoint::Expr)>,
    c: fixpoint::Constraint,
) -> fixpoint::Constraint {
    bindings.into_iter().rev().fold(c, |c, (var, sort, e)| {
        fixpoint::Constraint::ForAll(var, sort, fixpoint::Pred::Expr(e), Box::new(c))
    })
}

impl fmt::Debug for ConstraintBuilder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Constraint {{")?;
        writeln!(
            f,
            "    kvars: [{}]",
            self.kvars
                .iter_enumerated()
                .format_with(", ", |(kvid, sorts), f| f(&format_args!(
                    "KVar({:?}, {:?})",
                    kvid, sorts
                )))
        )?;

        writeln!(f, "    root: {:?}", PadAdapter::wrap(&self.root))?;
        writeln!(f, "}}")
    }
}

impl fmt::Debug for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            Node::Conj(children) => {
                write!(f, "Conj {{")?;
                debug_children(children, f)?;
                write!(f, "}}")
            }
            Node::ForAll(var, sort, pred, children) => {
                if pred.is_true() {
                    write!(f, "ForAll({:?}: {:?}) {{", var, sort)?;
                } else {
                    write!(f, "ForAll({:?}: {:?} {{ {:?} }}) {{", var, sort, pred)?;
                }
                debug_children(children, f)?;
                write!(f, "}}")
            }
            Node::Guard(expr, children) => {
                write!(f, "Guard({:?}) {{", expr)?;
                debug_children(children, f)?;
                write!(f, "}}")
            }
            Node::Head(pred) => {
                write!(f, "{:?}", pred)
            }
        }
    }
}

fn debug_children(children: &[Node], f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let mut w = PadAdapter::wrap_fmt(f);
    for child in children {
        write!(w, "\n{:?}", child)?;
    }
    if children.is_empty() {
        write!(f, " ")
    } else {
        writeln!(f)
    }
}

impl fmt::Debug for Cursor<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{{{}}}",
            self.vars_in_scope()
                .format_with(", ", |(var, sort), f| f(&format_args!(
                    "{:?}: {:?}",
                    var, sort
                )))
        )
    }
}
