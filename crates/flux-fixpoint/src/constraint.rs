use std::{
    fmt::{self, Write},
    sync::LazyLock,
};

use derive_where::derive_where;
use flux_common::format::PadAdapter;
use itertools::Itertools;
use rustc_macros::{Decodable, Encodable};

use crate::{big_int::BigInt, StringTypes, Types};

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

#[derive_where(Clone, Hash)]
pub enum Sort<T: Types> {
    Int,
    Bool,
    Real,
    Var(u32),
    BitVec(usize),
    Func(PolyFuncSort<T>),
    App(SortCtor<T>, Vec<Self>),
}

#[derive_where(Clone, Hash)]
pub enum SortCtor<T: Types> {
    Set,
    Map,
    Data(T::Sort),
}

#[derive_where(Clone, Hash)]
pub struct FuncSort<T: Types> {
    inputs_and_output: Vec<Sort<T>>,
}

#[derive_where(Clone, Hash)]
pub struct PolyFuncSort<T: Types> {
    params: usize,
    fsort: FuncSort<T>,
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
    Constant(Constant),
    Var(T::Var),
    App(T::Var, Vec<Self>),
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Encodable, Decodable)]
pub enum Constant {
    Int(BigInt),
    Real(i128),
    Bool(bool),
}

impl<T: Types> Constraint<T> {
    pub const TRUE: Self = Self::Pred(Pred::TRUE, None);

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

impl<T: Types> PolyFuncSort<T> {
    pub fn new(params: usize, mut inputs: Vec<Sort<T>>, output: Sort<T>) -> PolyFuncSort<T> {
        inputs.push(output);
        PolyFuncSort { params, fsort: FuncSort { inputs_and_output: inputs } }
    }
}

impl<T: Types> fmt::Display for DataDecl<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(data {} {} = [{}])", self.name, self.vars, self.ctors.iter().format(" "))
    }
}

impl<T: Types> fmt::Display for DataCtor<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "| {} {{ {} }}", self.name, self.fields.iter().format(", "))
    }
}

impl<T: Types> fmt::Display for DataField<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.name, self.sort)
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
                    write!(f, "({pred})")
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
            Sort::Var(i) => write!(f, "@({i})"),
            Sort::BitVec(size) => write!(f, "(BitVec Size{})", size),
            Sort::Func(sort) => write!(f, "{sort}"),
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

impl<T: Types> fmt::Display for PolyFuncSort<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(func({}, [{}]))", self.params, self.fsort.inputs_and_output.iter().format("; "))
    }
}

impl<T: Types> fmt::Display for FuncSort<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(func(0, [{}]))", self.inputs_and_output.iter().format("; "))
    }
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
    pub const ZERO: Expr<T> = Expr::Constant(Constant::ZERO);
    pub const ONE: Expr<T> = Expr::Constant(Constant::ONE);
    pub const TRUE: Expr<T> = Expr::Constant(Constant::TRUE);
    pub fn eq(self, other: Self) -> Self {
        Expr::Atom(BinRel::Eq, Box::new([self, other]))
    }
}

struct FmtParens<'a, T: Types>(&'a Expr<T>);

impl<T: Types> fmt::Display for FmtParens<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Avoid some obvious unnecesary parentheses
        let should_parenthesize =
            !matches!(&self.0, Expr::Var(_) | Expr::Constant(_) | Expr::App(..));
        if should_parenthesize {
            write!(f, "({})", self.0)
        } else {
            write!(f, "{}", self.0)
        }
    }
}

impl<T: Types> fmt::Display for Expr<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Constant(c) => write!(f, "{c}"),
            Expr::Var(x) => write!(f, "{x}"),
            Expr::App(func, args) => {
                write!(f, "({func} {})", args.iter().map(FmtParens).format(" "),)
            }
            Expr::Neg(e) => {
                write!(f, "-{}", FmtParens(e))
            }
            Expr::BinaryOp(op, box [e1, e2]) => {
                write!(f, "{} {op} {}", FmtParens(e1), FmtParens(e2))
            }
            Expr::IfThenElse(box [p, e1, e2]) => {
                write!(f, "if {p} then {e1} else {e2}")
            }
            Expr::And(exprs) => {
                write!(f, "{}", exprs.iter().map(FmtParens).format(" && "))
            }
            Expr::Or(exprs) => {
                write!(f, "{}", exprs.iter().map(FmtParens).format(" || "))
            }
            Expr::Not(e) => {
                write!(f, "~{}", FmtParens(e))
            }
            Expr::Imp(box [e1, e2]) => {
                write!(f, "{} => {}", FmtParens(e1), FmtParens(e2))
            }
            Expr::Iff(box [e1, e2]) => {
                write!(f, "{} <=> {}", FmtParens(e1), FmtParens(e2))
            }
            Expr::Atom(rel, box [e1, e2]) => {
                write!(f, "{} {rel} {}", FmtParens(e1), FmtParens(e2))
            }
        }
    }
}

pub(crate) static DEFAULT_QUALIFIERS: LazyLock<Vec<Qualifier<StringTypes>>> = LazyLock::new(|| {
    // -----
    // UNARY
    // -----

    // (qualif EqZero ((v int)) (v == 0))
    let eqzero = Qualifier {
        args: vec![("v", Sort::Int)],
        body: Expr::Atom(BinRel::Eq, Box::new([Expr::Var("v"), Expr::ZERO])),
        name: String::from("EqZero"),
    };

    // (qualif GtZero ((v int)) (v > 0))
    let gtzero = Qualifier {
        args: vec![("v", Sort::Int)],
        body: Expr::Atom(BinRel::Gt, Box::new([Expr::Var("v"), Expr::ZERO])),
        name: String::from("GtZero"),
    };

    // (qualif GeZero ((v int)) (v >= 0))
    let gezero = Qualifier {
        args: vec![("v", Sort::Int)],
        body: Expr::Atom(BinRel::Ge, Box::new([Expr::Var("v"), Expr::ZERO])),
        name: String::from("GeZero"),
    };

    // (qualif LtZero ((v int)) (v < 0))
    let ltzero = Qualifier {
        args: vec![("v", Sort::Int)],
        body: Expr::Atom(BinRel::Lt, Box::new([Expr::Var("v"), Expr::ZERO])),
        name: String::from("LtZero"),
    };

    // (qualif LeZero ((v int)) (v <= 0))
    let lezero = Qualifier {
        args: vec![("v", Sort::Int)],
        body: Expr::Atom(BinRel::Le, Box::new([Expr::Var("v"), Expr::ZERO])),
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
                Expr::BinaryOp(BinOp::Sub, Box::new([Expr::Var("b"), Expr::ONE])),
            ]),
        ),
        name: String::from("Le1"),
    };

    vec![eqzero, gtzero, gezero, ltzero, lezero, eq, gt, ge, lt, le, le1]
});

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
            BinRel::Ne => write!(f, "/="),
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

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constant::Int(n) => write!(f, "{n}"),
            Constant::Real(r) => write!(f, "{r}.0"),
            Constant::Bool(b) => write!(f, "{b}"),
        }
    }
}

impl Constant {
    pub const ZERO: Constant = Constant::Int(BigInt::ZERO);
    pub const ONE: Constant = Constant::Int(BigInt::ONE);
    pub const TRUE: Constant = Constant::Bool(true);

    fn to_bool(self) -> Option<bool> {
        match self {
            Constant::Bool(b) => Some(b),
            _ => None,
        }
    }

    fn to_int(self) -> Option<BigInt> {
        match self {
            Constant::Int(n) => Some(n),
            _ => None,
        }
    }

    pub fn iff(&self, other: &Constant) -> Option<Constant> {
        let b1 = self.to_bool()?;
        let b2 = other.to_bool()?;
        Some(Constant::Bool(b1 == b2))
    }

    pub fn imp(&self, other: &Constant) -> Option<Constant> {
        let b1 = self.to_bool()?;
        let b2 = other.to_bool()?;
        Some(Constant::Bool(!b1 || b2))
    }

    pub fn or(&self, other: &Constant) -> Option<Constant> {
        let b1 = self.to_bool()?;
        let b2 = other.to_bool()?;
        Some(Constant::Bool(b1 || b2))
    }

    pub fn and(&self, other: &Constant) -> Option<Constant> {
        let b1 = self.to_bool()?;
        let b2 = other.to_bool()?;
        Some(Constant::Bool(b1 && b2))
    }

    pub fn eq(&self, other: &Constant) -> Constant {
        Constant::Bool(*self == *other)
    }

    pub fn ne(&self, other: &Constant) -> Constant {
        Constant::Bool(*self != *other)
    }

    pub fn gt(&self, other: &Constant) -> Option<Constant> {
        let n1 = self.to_int()?;
        let n2 = other.to_int()?;
        Some(Constant::Bool(n1 > n2))
    }

    pub fn ge(&self, other: &Constant) -> Option<Constant> {
        let n1 = self.to_int()?;
        let n2 = other.to_int()?;
        Some(Constant::Bool(n1 >= n2))
    }

    /// See [`BigInt::int_min`]
    pub fn int_min(bit_width: u32) -> Constant {
        Constant::Int(BigInt::int_min(bit_width))
    }

    /// See [`BigInt::int_max`]
    pub fn int_max(bit_width: u32) -> Constant {
        Constant::Int(BigInt::int_max(bit_width))
    }

    /// See [`BigInt::uint_max`]
    pub fn uint_max(bit_width: u32) -> Constant {
        Constant::Int(BigInt::uint_max(bit_width))
    }
}

impl From<i32> for Constant {
    fn from(c: i32) -> Self {
        Constant::Int(c.into())
    }
}

impl From<usize> for Constant {
    fn from(u: usize) -> Self {
        Constant::Int(u.into())
    }
}

impl From<u128> for Constant {
    fn from(c: u128) -> Self {
        Constant::Int(c.into())
    }
}

impl From<i128> for Constant {
    fn from(c: i128) -> Self {
        Constant::Int(c.into())
    }
}

impl From<bool> for Constant {
    fn from(b: bool) -> Self {
        Constant::Bool(b)
    }
}
