use std::{
    fmt::{self, Write},
    sync::LazyLock,
};

use derive_where::derive_where;
use flux_common::format::PadAdapter;
use itertools::Itertools;

use crate::{DefaultTypes, Types};

#[derive_where(Hash)]
pub struct Bind<T: Types> {
    pub name: T::Var,
    pub sort: Sort<T>,
    pub pred: Pred<T>,
}

#[derive_where(Hash)]
pub enum Constraint<T: Types> {
    Pred(Pred<T>, #[derive_where(skip)] Option<T::Tag>),
    Conj(Vec<Self>),
    ForAll(Bind<T>, Box<Self>),
}

#[derive_where(Hash)]
pub struct DataDecl<T: Types> {
    pub name: T::Sort,
    pub vars: usize,
    pub ctors: Vec<DataCtor<T>>,
}

#[derive_where(Hash)]
pub struct DataCtor<T: Types> {
    pub name: T::Var,
    pub fields: Vec<DataField<T>>,
}

#[derive_where(Hash)]
pub struct DataField<T: Types> {
    pub name: T::Var,
    pub sort: Sort<T>,
}

#[derive_where(Hash, Clone)]
pub enum Sort<T: Types> {
    Int,
    Bool,
    Real,
    Str,
    BitVec(Box<Sort<T>>),
    BvSize(usize),
    Var(usize),
    Func(Box<[Self; 2]>),
    Abs(usize, Box<Self>),
    App(SortCtor<T>, Vec<Self>),
}

impl<T: Types> Sort<T> {
    pub fn mk_func<I>(params: usize, inputs: I, output: Sort<T>) -> Sort<T>
    where
        I: IntoIterator<Item = Sort<T>>,
        I::IntoIter: DoubleEndedIterator,
    {
        let sort = inputs
            .into_iter()
            .rev()
            .fold(output, |output, input| Sort::Func(Box::new([input, output])));

        (0..params)
            .rev()
            .fold(sort, |sort, i| Sort::Abs(i, Box::new(sort)))
    }

    fn peel_out_abs(&self) -> (usize, &Sort<T>) {
        let mut n = 0;
        let mut curr = self;
        while let Sort::Abs(i, sort) = curr {
            assert_eq!(*i, n);
            n += 1;
            curr = sort;
        }
        (n, curr)
    }
}

#[derive_where(Hash, Clone)]
pub enum SortCtor<T: Types> {
    Set,
    Map,
    Data(T::Sort),
}

#[derive_where(Hash)]
pub enum Pred<T: Types> {
    And(Vec<Self>),
    KVar(T::KVar, Vec<T::Var>),
    Expr(Expr<T>),
}

#[derive(Hash, Debug, Copy, Clone, PartialEq, Eq)]
pub enum BinRel {
    Eq,
    Ne,
    Gt,
    Ge,
    Lt,
    Le,
}

impl BinRel {
    pub const INEQUALITIES: [BinRel; 4] = [BinRel::Gt, BinRel::Ge, BinRel::Lt, BinRel::Le];
}

#[derive_where(Hash)]
pub enum Expr<T: Types> {
    Constant(Constant<T>),
    Var(T::Var),
    App(Box<Self>, Vec<Self>),
    Neg(Box<Self>),
    BinaryOp(BinOp, Box<[Self; 2]>),
    IfThenElse(Box<[Self; 3]>),
    And(Vec<Expr<T>>),
    Or(Vec<Expr<T>>),
    Not(Box<Self>),
    Imp(Box<[Expr<T>; 2]>),
    Iff(Box<[Expr<T>; 2]>),
    Atom(BinRel, Box<[Self; 2]>),
}

#[derive_where(Hash)]
pub enum Constant<T: Types> {
    Int(T::IntLit),
    Real(T::RealLit),
    Bool(bool),
    Str(T::StrLit),
}

#[derive_where(Hash)]
pub struct Qualifier<T: Types> {
    pub name: String,
    pub args: Vec<(T::Var, Sort<T>)>,
    pub body: Expr<T>,
}

#[derive(Clone, Copy)]
pub struct Const<T: Types> {
    pub name: T::Var,
    pub val: i128,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

impl<T: Types> Constraint<T> {
    pub const TRUE: Self = Self::Pred(Pred::TRUE, None);

    pub fn foralls(bindings: Vec<Bind<T>>, c: Self) -> Self {
        bindings
            .into_iter()
            .rev()
            .fold(c, |c, bind| Constraint::ForAll(bind, Box::new(c)))
    }

    /// Returns true if the constraint has at least one concrete RHS ("head") predicates.
    /// If `!c.is_concrete`  then `c` is trivially satisfiable and we can avoid calling fixpoint.
    pub fn is_concrete(&self) -> bool {
        match self {
            Constraint::Conj(cs) => cs.iter().any(Constraint::is_concrete),
            Constraint::ForAll(_, c) => c.is_concrete(),
            Constraint::Pred(p, _) => p.is_concrete() && !p.is_trivially_true(),
        }
    }
}

impl<T: Types> Pred<T> {
    pub const TRUE: Self = Pred::Expr(Expr::Constant(Constant::Bool(true)));

    pub fn is_trivially_true(&self) -> bool {
        match self {
            Pred::Expr(Expr::Constant(Constant::Bool(true))) => true,
            Pred::And(ps) => ps.is_empty(),
            _ => false,
        }
    }

    pub fn is_concrete(&self) -> bool {
        match self {
            Pred::And(ps) => ps.iter().any(Pred::is_concrete),
            Pred::KVar(_, _) => false,
            Pred::Expr(_) => true,
        }
    }
}

pub(crate) static DEFAULT_QUALIFIERS: LazyLock<Vec<Qualifier<DefaultTypes>>> =
    LazyLock::new(|| {
        // -----
        // UNARY
        // -----

        // (qualif EqZero ((v int)) (v == 0))
        let eqzero = Qualifier {
            args: vec![("v", Sort::Int)],
            body: Expr::Atom(BinRel::Eq, Box::new([Expr::Var("v"), Expr::int(0)])),
            name: String::from("EqZero"),
        };

        // (qualif GtZero ((v int)) (v > 0))
        let gtzero = Qualifier {
            args: vec![("v", Sort::Int)],
            body: Expr::Atom(BinRel::Gt, Box::new([Expr::Var("v"), Expr::int(0)])),
            name: String::from("GtZero"),
        };

        // (qualif GeZero ((v int)) (v >= 0))
        let gezero = Qualifier {
            args: vec![("v", Sort::Int)],
            body: Expr::Atom(BinRel::Ge, Box::new([Expr::Var("v"), Expr::int(0)])),
            name: String::from("GeZero"),
        };

        // (qualif LtZero ((v int)) (v < 0))
        let ltzero = Qualifier {
            args: vec![("v", Sort::Int)],
            body: Expr::Atom(BinRel::Lt, Box::new([Expr::Var("v"), Expr::int(0)])),
            name: String::from("LtZero"),
        };

        // (qualif LeZero ((v int)) (v <= 0))
        let lezero = Qualifier {
            args: vec![("v", Sort::Int)],
            body: Expr::Atom(BinRel::Le, Box::new([Expr::Var("v"), Expr::int(0)])),
            name: String::from("LeZero"),
        };

        // ------
        // BINARY
        // ------

        // (qualif Eq ((a int) (b int)) (a == b))
        let eq = Qualifier {
            args: vec![("a", Sort::Int), ("b", Sort::Int)],
            body: Expr::Atom(BinRel::Eq, Box::new([Expr::Var("a"), Expr::Var("b")])),
            name: String::from("Eq"),
        };

        // (qualif Gt ((a int) (b int)) (a > b))
        let gt = Qualifier {
            args: vec![("a", Sort::Int), ("b", Sort::Int)],
            body: Expr::Atom(BinRel::Gt, Box::new([Expr::Var("a"), Expr::Var("b")])),
            name: String::from("Gt"),
        };

        // (qualif Lt ((a int) (b int)) (a < b))
        let ge = Qualifier {
            args: vec![("a", Sort::Int), ("b", Sort::Int)],
            body: Expr::Atom(BinRel::Ge, Box::new([Expr::Var("a"), Expr::Var("b")])),
            name: String::from("Ge"),
        };

        // (qualif Ge ((a int) (b int)) (a >= b))
        let lt = Qualifier {
            args: vec![("a", Sort::Int), ("b", Sort::Int)],
            body: Expr::Atom(BinRel::Lt, Box::new([Expr::Var("a"), Expr::Var("b")])),
            name: String::from("Lt"),
        };

        // (qualif Le ((a int) (b int)) (a <= b))
        let le = Qualifier {
            args: vec![("a", Sort::Int), ("b", Sort::Int)],
            body: Expr::Atom(BinRel::Le, Box::new([Expr::Var("a"), Expr::Var("b")])),
            name: String::from("Le"),
        };

        // (qualif Le1 ((a int) (b int)) (a < b - 1))
        let le1 = Qualifier {
            args: vec![("a", Sort::Int), ("b", Sort::Int)],
            body: Expr::Atom(
                BinRel::Le,
                Box::new([
                    Expr::Var("a"),
                    Expr::BinaryOp(BinOp::Sub, Box::new([Expr::Var("b"), Expr::int(1)])),
                ]),
            ),
            name: String::from("Le1"),
        };

        vec![eqzero, gtzero, gezero, ltzero, lezero, eq, gt, ge, lt, le, le1]
    });

impl<T: Types> fmt::Display for DataDecl<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(datatype ({} {}) ({}))", self.name, self.vars, self.ctors.iter().format(" "))
    }
}

impl<T: Types> fmt::Display for DataCtor<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} ({}))", self.name, self.fields.iter().format(" "))
    }
}

impl<T: Types> fmt::Display for DataField<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({} {})", self.name, self.sort)
    }
}

impl<T: Types> fmt::Display for Constraint<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constraint::Pred(pred, tag) => write!(f, "{}", PredTag(pred, tag)),
            Constraint::Conj(preds) => {
                match &preds[..] {
                    [] => write!(f, "((true))"),
                    [pred] => write!(f, "{pred}"),
                    preds => {
                        write!(f, "(and")?;
                        write!(PadAdapter::wrap_fmt(f, 2), "\n{}", preds.iter().join("\n"))?;
                        write!(f, "\n)")
                    }
                }
            }
            Constraint::ForAll(bind, head) => {
                write!(f, "(forall (({} {}) {})", bind.name, bind.sort, bind.pred)?;
                write!(PadAdapter::wrap_fmt(f, 2), "\n{head}")?;
                write!(f, "\n)")
            }
        }
    }
}

struct PredTag<'a, T: Types>(&'a Pred<T>, &'a Option<T::Tag>);

impl<T: Types> fmt::Display for PredTag<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let PredTag(pred, tag) = self;
        match pred {
            Pred::And(preds) => {
                match &preds[..] {
                    [] => write!(f, "((true))"),
                    [pred] => write!(f, "{}", PredTag(pred, tag)),
                    _ => {
                        write!(f, "(and")?;
                        let mut w = PadAdapter::wrap_fmt(f, 2);
                        for pred in preds {
                            write!(w, "\n{}", PredTag(pred, tag))?;
                        }
                        write!(f, "\n)")
                    }
                }
            }
            Pred::Expr(_) | Pred::KVar(..) => {
                if let Some(tag) = tag {
                    write!(f, "(tag {pred} \"{tag}\")")
                } else {
                    write!(f, "{pred}")
                }
            }
        }
    }
}

impl<T: Types> fmt::Display for SortCtor<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SortCtor::Set => write!(f, "Set_Set"),
            SortCtor::Map => write!(f, "Map_t"),
            SortCtor::Data(name) => write!(f, "{name}"),
        }
    }
}

impl<T: Types> fmt::Display for Sort<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sort::Int => write!(f, "int"),
            Sort::Bool => write!(f, "bool"),
            Sort::Real => write!(f, "real"),
            Sort::Str => write!(f, "Str"),
            Sort::Var(i) => write!(f, "@({i})"),
            Sort::BitVec(size) => write!(f, "(BitVec {size})"),
            Sort::BvSize(size) => write!(f, "Size{size}"),
            Sort::Abs(..) => {
                let (params, sort) = self.peel_out_abs();
                fmt_func(params, sort, f)
            }
            Sort::Func(..) => fmt_func(0, self, f),
            Sort::App(ctor, args) => {
                write!(f, "({ctor}")?;
                for arg in args {
                    write!(f, " {arg}")?;
                }
                write!(f, ")")
            }
        }
    }
}

fn fmt_func<T: Types>(params: usize, sort: &Sort<T>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    write!(f, "(func {params} (")?;
    let mut curr = sort;
    while let Sort::Func(box [input, output]) = curr {
        write!(f, "{input} ")?;
        curr = output;
    }
    write!(f, ") {curr})")
}

impl<T: Types> fmt::Display for Pred<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Pred::And(preds) => {
                match &preds[..] {
                    [] => write!(f, "((true))"),
                    [pred] => write!(f, "{pred}"),
                    preds => write!(f, "(and {})", preds.iter().join(" ")),
                }
            }
            Pred::KVar(kvid, vars) => {
                write!(f, "(${kvid} {})", vars.iter().format(" "))
            }
            Pred::Expr(expr) => write!(f, "({expr})"),
        }
    }
}

impl<T: Types> Expr<T> {
    pub const fn int(val: T::IntLit) -> Expr<T> {
        Expr::Constant(Constant::Int(val))
    }

    pub fn eq(self, other: Self) -> Self {
        Expr::Atom(BinRel::Eq, Box::new([self, other]))
    }
}

impl<T: Types> fmt::Display for Expr<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Constant(c) => write!(f, "{c}"),
            Expr::Var(x) => write!(f, "{x}"),
            Expr::App(func, args) => {
                write!(f, "({func} {})", args.iter().format(" "))
            }
            Expr::Neg(e) => {
                write!(f, "(- {e})")
            }
            Expr::BinaryOp(op, box [e1, e2]) => {
                write!(f, "({op} {e1} {e2})")
            }
            Expr::IfThenElse(box [p, e1, e2]) => {
                write!(f, "(if {p} {e1} {e2})")
            }
            Expr::And(exprs) => {
                write!(f, "(and {})", exprs.iter().format(" "))
            }
            Expr::Or(exprs) => {
                write!(f, "(or {})", exprs.iter().format(" "))
            }
            Expr::Not(e) => {
                write!(f, "(not {e})")
            }
            Expr::Imp(box [e1, e2]) => {
                write!(f, "(=> {e1} {e2})")
            }
            Expr::Iff(box [e1, e2]) => {
                write!(f, "(<=> {e1} {e2})")
            }
            Expr::Atom(rel, box [e1, e2]) => {
                write!(f, "({rel} {e1} {e2})")
            }
        }
    }
}

impl<T: Types> fmt::Display for Constant<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constant::Int(i) => write!(f, "{i}"),
            Constant::Real(r) => write!(f, "{r}"),
            Constant::Bool(b) => write!(f, "{b}"),
            Constant::Str(s) => write!(f, "{s}"),
        }
    }
}

impl<T: Types> fmt::Display for Qualifier<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "(qualif {} ({}) ({}))",
            self.name,
            self.args
                .iter()
                .format_with(" ", |(name, sort), f| f(&format_args!("({name} {sort})"))),
            self.body
        )
    }
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinOp::Add => write!(f, "+"),
            BinOp::Sub => write!(f, "-"),
            BinOp::Mul => write!(f, "*"),
            BinOp::Div => write!(f, "/"),
            BinOp::Mod => write!(f, "mod"),
        }
    }
}

impl fmt::Display for BinRel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinRel::Eq => write!(f, "="),
            BinRel::Ne => write!(f, "!="),
            BinRel::Gt => write!(f, ">"),
            BinRel::Ge => write!(f, ">="),
            BinRel::Lt => write!(f, "<"),
            BinRel::Le => write!(f, "<="),
        }
    }
}

impl fmt::Debug for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}
