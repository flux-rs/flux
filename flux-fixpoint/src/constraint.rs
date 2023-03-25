use std::{
    fmt::{self, Write},
    hash::{Hash, Hasher},
    sync::LazyLock,
};

use flux_common::format::PadAdapter;
use itertools::Itertools;
use rustc_index::newtype_index;
use rustc_macros::{Decodable, Encodable};
use rustc_span::Symbol;

pub enum Constraint<Tag> {
    Pred(Pred, Option<Tag>),
    Conj(Vec<Self>),
    Guard(Pred, Box<Self>),
    ForAll(Name, Sort, Pred, Box<Self>),
}

#[derive(Clone, Hash)]
pub enum Sort {
    Int,
    Bool,
    Real,
    Unit,
    BitVec(usize),
    Pair(Box<Sort>, Box<Sort>),
    Func(FuncSort),
}

#[derive(Clone, Hash)]
pub struct FuncSort {
    inputs_and_output: Vec<Sort>,
}

#[derive(Hash)]
pub enum Pred {
    And(Vec<Self>),
    KVar(KVid, Vec<Name>),
    Expr(Expr),
}

#[derive(Hash)]
pub enum Expr {
    Var(Name),
    ConstVar(ConstName),
    Constant(Constant),
    BinaryOp(BinOp, Box<[Expr; 2]>),
    App(Func, Vec<Expr>),
    UnaryOp(UnOp, Box<Self>),
    Pair(Box<[Expr; 2]>),
    Proj(Box<Expr>, Proj),
    IfThenElse(Box<[Expr; 3]>),
    Unit,
}

#[derive(Hash, Debug, Clone)]
pub enum Func {
    Var(Name),
    /// uninterepreted function
    Uif(ConstName),
    /// interpreted (theory) function
    Itf(Symbol),
}

#[derive(Clone, Copy, Hash)]
pub enum Proj {
    Fst,
    Snd,
}

#[derive(Hash)]
pub struct Qualifier {
    pub name: String,
    pub args: Vec<(Name, Sort)>,
    pub body: Expr,
    pub global: bool,
}

#[derive(Clone, Copy, Debug)]
pub struct Const {
    pub name: ConstName,
    pub val: i128,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Encodable, Decodable)]
pub enum BinOp {
    Iff,
    Imp,
    Or,
    And,
    Eq,
    Ne,
    Gt,
    Ge,
    Lt,
    Le,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Encodable, Decodable)]
pub enum UnOp {
    Not,
    Neg,
}

#[derive(Clone, Debug, Copy, PartialEq, Eq, Hash, Encodable, Decodable)]
pub enum Constant {
    Int(Sign, u128),
    Real(i128),
    Bool(bool),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Encodable, Decodable)]
pub enum Sign {
    Positive,
    Negative,
}

newtype_index! {
    #[debug_format = "$k{}"]
    pub struct KVid {}
}

newtype_index! {
    #[debug_format = "a{}"]
    pub struct Name {
        const NAME0 = 0;
        const NAME1 = 1;
        const NAME2 = 2;
    }
}

newtype_index! {
    #[debug_format = "c{}"]
    pub struct ConstName {}
}

impl<Tag> Constraint<Tag> {
    pub const TRUE: Self = Self::Pred(Pred::TRUE, None);

    /// Returns true if the constraint has at least one concrete RHS ("head") predicates.
    /// If `!c.is_concrete`  then `c` is trivially satisfiable and we can avoid calling fixpoint.
    pub fn is_concrete(&self) -> bool {
        match self {
            Constraint::Conj(cs) => cs.iter().any(Constraint::is_concrete),
            Constraint::Guard(_, c) | Constraint::ForAll(_, _, _, c) => c.is_concrete(),
            Constraint::Pred(p, _) => p.is_concrete() && !p.is_trivially_true(),
        }
    }
}

impl<Tag> Hash for Constraint<Tag> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let tag = std::mem::discriminant(self);
        tag.hash(state);
        match self {
            Constraint::Pred(p, _) => p.hash(state),
            Constraint::Conj(cs) => cs.hash(state),
            Constraint::Guard(p, c) => {
                p.hash(state);
                c.hash(state);
            }
            Constraint::ForAll(x, t, p, c) => {
                x.hash(state);
                t.hash(state);
                p.hash(state);
                c.hash(state);
            }
        }
    }
}

impl Pred {
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

impl FuncSort {
    pub fn new(inputs: impl IntoIterator<Item = Sort>, output: Sort) -> FuncSort {
        let mut inputs = inputs.into_iter().collect_vec();
        inputs.push(output);
        FuncSort { inputs_and_output: inputs }
    }
}

impl<Tag> fmt::Display for Constraint<Tag>
where
    Tag: fmt::Display,
{
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
            Constraint::Guard(body, head) => {
                write!(f, "(forall ((_ Unit) {body})")?;
                write!(PadAdapter::wrap_fmt(f, 2), "\n{head}")?;
                write!(f, "\n)")
            }
            Constraint::ForAll(x, sort, body, head) => {
                write!(f, "(forall (({x:?} {sort}) {body})")?;
                write!(PadAdapter::wrap_fmt(f, 2), "\n{head}")?;
                write!(f, "\n)")
            }
        }
    }
}

struct PredTag<'a, Tag>(&'a Pred, &'a Option<Tag>);

impl<Tag> fmt::Display for PredTag<'_, Tag>
where
    Tag: fmt::Display,
{
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

impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Sort::Int => write!(f, "int"),
            Sort::Bool => write!(f, "bool"),
            Sort::Real => write!(f, "real"),
            Sort::Unit => write!(f, "Unit"),
            Sort::BitVec(size) => write!(f, "(BitVec Size{})", size),
            Sort::Pair(s1, s2) => write!(f, "(Pair {s1} {s2})"),
            Sort::Func(sort) => write!(f, "{sort}"),
        }
    }
}

impl fmt::Display for FuncSort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(func(0, [{:?}]))", self.inputs_and_output.iter().format("; "))
    }
}

impl fmt::Debug for Sort {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for Pred {
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
                write!(f, "({kvid:?} {:?})", vars.iter().format(" "))
            }
            Pred::Expr(expr) => write!(f, "({expr})"),
        }
    }
}

impl Expr {
    pub const ZERO: Expr = Expr::Constant(Constant::ZERO);
    pub const ONE: Expr = Expr::Constant(Constant::ONE);
    pub fn eq(self, other: Expr) -> Expr {
        Expr::BinaryOp(BinOp::Eq, Box::new([self, other]))
    }
}

struct FmtParens<'a>(&'a Expr);

impl fmt::Display for FmtParens<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Fixpoint parser has `=` at two different precedence levels depending on whether it is
        // used in a sequence of boolean expressions or not. To avoid complexity we parenthesize
        // all binary expressions no matter the parent operator.
        let should_parenthesize = matches!(&self.0, Expr::BinaryOp(..) | Expr::IfThenElse(..));
        if should_parenthesize {
            write!(f, "({})", self.0)
        } else {
            write!(f, "{}", self.0)
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Var(x) => write!(f, "{x:?}"),
            Expr::ConstVar(x) => write!(f, "{x:?}"),
            Expr::Constant(c) => write!(f, "{c}"),
            Expr::BinaryOp(op, box [e1, e2]) => {
                write!(f, "{} {op} {}", FmtParens(e1), FmtParens(e2))?;
                Ok(())
            }
            Expr::UnaryOp(op, e) => {
                if matches!(e.as_ref(), Expr::Constant(_) | Expr::Var(_)) {
                    write!(f, "{op}{e}")
                } else {
                    write!(f, "{op}({e})")
                }
            }
            Expr::Pair(box [e1, e2]) => write!(f, "(Pair ({e1}) ({e2}))"),
            Expr::Proj(e, Proj::Fst) => write!(f, "(fst {e})"),
            Expr::Proj(e, Proj::Snd) => write!(f, "(snd {e})"),
            Expr::Unit => write!(f, "Unit"),
            Expr::App(func, args) => {
                write!(f, "({func} {})", args.iter().map(FmtParens).format(" "),)
            }
            Expr::IfThenElse(box [p, e1, e2]) => {
                write!(f, "if {p} then {e1} else {e2}")
            }
        }
    }
}

impl fmt::Display for Func {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Func::Var(name) => write!(f, "{name:?}"),
            Func::Uif(uif) => write!(f, "{uif:?}"),
            Func::Itf(itf) => write!(f, "{itf}"),
        }
    }
}

pub(crate) static DEFAULT_QUALIFIERS: LazyLock<Vec<Qualifier>> = LazyLock::new(|| {
    // Unary

    // (qualif EqZero ((v int)) (v == 0))
    let eqzero = Qualifier {
        args: vec![(NAME0, Sort::Int)],
        body: Expr::BinaryOp(BinOp::Eq, Box::new([Expr::Var(NAME0), Expr::ZERO])),
        name: String::from("EqZero"),
        global: true,
    };

    // (qualif GtZero ((v int)) (v > 0))
    let gtzero = Qualifier {
        args: vec![(NAME0, Sort::Int)],
        body: Expr::BinaryOp(BinOp::Gt, Box::new([Expr::Var(NAME0), Expr::ZERO])),
        name: String::from("GtZero"),
        global: true,
    };

    // (qualif GeZero ((v int)) (v >= 0))
    let gezero = Qualifier {
        args: vec![(NAME0, Sort::Int)],
        body: Expr::BinaryOp(BinOp::Ge, Box::new([Expr::Var(NAME0), Expr::ZERO])),
        name: String::from("GeZero"),
        global: true,
    };

    // (qualif LtZero ((v int)) (v < 0))
    let ltzero = Qualifier {
        args: vec![(NAME0, Sort::Int)],
        body: Expr::BinaryOp(BinOp::Lt, Box::new([Expr::Var(NAME0), Expr::ZERO])),
        name: String::from("LtZero"),
        global: true,
    };

    // (qualif LeZero ((v int)) (v <= 0))
    let lezero = Qualifier {
        args: vec![(NAME0, Sort::Int)],
        body: Expr::BinaryOp(BinOp::Le, Box::new([Expr::Var(NAME0), Expr::ZERO])),
        name: String::from("LeZero"),
        global: true,
    };

    // Binary

    // (qualif Eq ((a int) (b int)) (a == b))
    let eq = Qualifier {
        args: vec![(NAME0, Sort::Int), (NAME1, Sort::Int)],
        body: Expr::BinaryOp(BinOp::Eq, Box::new([Expr::Var(NAME0), Expr::Var(NAME1)])),
        name: String::from("Eq"),
        global: true,
    };

    // (qualif Gt ((a int) (b int)) (a > b))
    let gt = Qualifier {
        args: vec![(NAME0, Sort::Int), (NAME1, Sort::Int)],
        body: Expr::BinaryOp(BinOp::Gt, Box::new([Expr::Var(NAME0), Expr::Var(NAME1)])),
        name: String::from("Gt"),
        global: true,
    };

    // (qualif Lt ((a int) (b int)) (a < b))
    let ge = Qualifier {
        args: vec![(NAME0, Sort::Int), (NAME1, Sort::Int)],
        body: Expr::BinaryOp(BinOp::Ge, Box::new([Expr::Var(NAME0), Expr::Var(NAME1)])),
        name: String::from("Ge"),
        global: true,
    };

    // (qualif Ge ((a int) (b int)) (a >= b))
    let lt = Qualifier {
        args: vec![(NAME0, Sort::Int), (NAME1, Sort::Int)],
        body: Expr::BinaryOp(BinOp::Lt, Box::new([Expr::Var(NAME0), Expr::Var(NAME1)])),
        name: String::from("Lt"),
        global: true,
    };

    // (qualif Le ((a int) (b int)) (a <= b))
    let le = Qualifier {
        args: vec![(NAME0, Sort::Int), (NAME1, Sort::Int)],
        body: Expr::BinaryOp(BinOp::Le, Box::new([Expr::Var(NAME0), Expr::Var(NAME1)])),
        name: String::from("Le"),
        global: true,
    };

    // (qualif Le1 ((a int) (b int)) (a < b - 1))
    let le1 = Qualifier {
        args: vec![(NAME0, Sort::Int), (NAME1, Sort::Int)],
        body: Expr::BinaryOp(
            BinOp::Le,
            Box::new([
                Expr::Var(NAME0),
                Expr::BinaryOp(BinOp::Sub, Box::new([Expr::Var(NAME1), Expr::ONE])),
            ]),
        ),
        name: String::from("Le1"),
        global: true,
    };

    // (qualif Add2 ((a int) (b int) (c int)) (a == b + c))
    let _add2 = Qualifier {
        args: vec![(NAME0, Sort::Int), (NAME1, Sort::Int), (NAME2, Sort::Int)],
        body: Expr::BinaryOp(
            BinOp::Eq,
            Box::new([
                Expr::Var(NAME0),
                Expr::BinaryOp(BinOp::Add, Box::new([Expr::Var(NAME1), Expr::Var(NAME2)])),
            ]),
        ),
        name: String::from("Add2"),
        global: true,
    };

    // (qualif Sub2 ((a int) (b int) (c int)) (a == b - c))
    let _sub2 = Qualifier {
        args: vec![(NAME0, Sort::Int), (NAME1, Sort::Int), (NAME2, Sort::Int)],
        body: Expr::BinaryOp(
            BinOp::Eq,
            Box::new([
                Expr::Var(NAME0),
                Expr::BinaryOp(BinOp::Sub, Box::new([Expr::Var(NAME1), Expr::Var(NAME2)])),
            ]),
        ),
        name: String::from("Sub2"),
        global: true,
    };

    vec![eqzero, gtzero, gezero, ltzero, lezero, eq, gt, ge, lt, le, le1] //, add2, sub2]
});

impl fmt::Display for Qualifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "(qualif {} ({}) ({}))",
            self.name,
            self.args
                .iter()
                .format_with(" ", |(name, sort), f| f(&format_args!("({name:?} {sort})"))),
            self.body
        )
    }
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BinOp::Iff => write!(f, "<=>"),
            BinOp::Imp => write!(f, "=>"),
            BinOp::Or => write!(f, "||"),
            BinOp::And => write!(f, "&&"),
            BinOp::Eq => write!(f, "="),
            BinOp::Ne => write!(f, "/="),
            BinOp::Gt => write!(f, ">"),
            BinOp::Ge => write!(f, ">="),
            BinOp::Lt => write!(f, "<"),
            BinOp::Le => write!(f, "<="),
            BinOp::Add => write!(f, "+"),
            BinOp::Sub => write!(f, "-"),
            BinOp::Mul => write!(f, "*"),
            BinOp::Div => write!(f, "/"),
            BinOp::Mod => write!(f, "mod"),
        }
    }
}

impl fmt::Debug for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for UnOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnOp::Not => write!(f, "~"),
            UnOp::Neg => write!(f, "-"),
        }
    }
}

impl fmt::Debug for UnOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constant::Int(Sign::Positive, n) => write!(f, "{n}"),
            Constant::Int(Sign::Negative, n) => write!(f, "-{n}"),
            Constant::Real(r) => write!(f, "{r}.0"),
            Constant::Bool(b) => write!(f, "{b}"),
        }
    }
}

impl Constant {
    pub const ZERO: Constant = Constant::Int(Sign::Positive, 0);
    pub const ONE: Constant = Constant::Int(Sign::Positive, 1);

    fn to_bool(self) -> Option<bool> {
        match self {
            Constant::Bool(b) => Some(b),
            _ => None,
        }
    }

    /// Converts to an i128 and returns None if there is an overflow
    fn to_int(self) -> Option<i128> {
        match self {
            Constant::Int(Sign::Positive, n) => i128::try_from(n).ok(),
            Constant::Int(Sign::Negative, n) => Some(-(i128::try_from(n).ok()?)),
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

    /// Given the bit width of an integer type, produces the maximum integer for
    /// that type.
    pub fn int_min(bit_width: u32) -> Constant {
        let abs_max: u128 = 2_u128.pow(bit_width);
        Constant::Int(Sign::Negative, abs_max)
    }

    /// Given the bit width of an integer type, produces the minimum integer for
    /// that type.
    pub fn int_max(bit_width: u32) -> Constant {
        (i128::MAX >> (128 - bit_width)).into()
    }

    /// Given the bit width of an unsigned integer type, produces the maximum
    /// unsigned integer for that type.
    pub fn uint_max(bit_width: u32) -> Constant {
        (u128::MAX >> (128 - bit_width)).into()
    }
}

impl From<usize> for Constant {
    fn from(u: usize) -> Self {
        Constant::Int(Sign::Positive, u as u128)
    }
}

impl From<u128> for Constant {
    fn from(c: u128) -> Self {
        Constant::Int(Sign::Positive, c)
    }
}

impl From<i128> for Constant {
    fn from(c: i128) -> Self {
        let sign = if c < 0 { Sign::Negative } else { Sign::Positive };
        Constant::Int(sign, c.unsigned_abs())
    }
}

impl From<bool> for Constant {
    fn from(b: bool) -> Self {
        Constant::Bool(b)
    }
}

impl From<i128> for Expr {
    fn from(c: i128) -> Self {
        Expr::Constant(Constant::from(c))
    }
}

impl From<Name> for Expr {
    fn from(n: Name) -> Self {
        Expr::Var(n)
    }
}

impl From<ConstName> for Expr {
    fn from(c_n: ConstName) -> Self {
        Expr::ConstVar(c_n)
    }
}
