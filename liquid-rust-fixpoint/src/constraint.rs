use itertools::Itertools;
use rustc_index::newtype_index;
use std::{
    fmt::{self, Write},
    lazy::SyncLazy,
};

use liquid_rust_common::format::PadAdapter;

pub enum Constraint<Tag> {
    Pred(Pred, Option<Tag>),
    Conj(Vec<Self>),
    Guard(Expr, Box<Self>),
    ForAll(Name, Sort, Pred, Box<Self>),
}

#[derive(Clone)]
pub enum Sort {
    Int,
    Bool,
    Unit,
    Pair(Box<Sort>, Box<Sort>),
}

pub enum Pred {
    And(Vec<Self>),
    KVar(KVid, Vec<Name>),
    Expr(Expr),
}

pub enum Expr {
    Var(Name),
    Constant(Constant),
    BinaryOp(BinOp, Box<Self>, Box<Self>),
    UnaryOp(UnOp, Box<Self>),
    Pair(Box<Expr>, Box<Expr>),
    Proj(Box<Expr>, Proj),
    Unit,
}

#[derive(Clone, Copy)]
pub enum Proj {
    Fst,
    Snd,
}

pub struct Qualifier {
    pub expr: Expr,
    pub args: Vec<(Name, Sort)>,
    pub name: String,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
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

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnOp {
    Not,
    Neg,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Constant {
    Int(Sign, u128),
    Bool(bool),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Sign {
    Positive,
    Negative,
}

#[derive(PartialEq, Eq, PartialOrd, Ord)]
pub enum Precedence {
    Iff,
    Imp,
    Or,
    And,
    Cmp,
    AddSub,
    MulDiv,
}

newtype_index! {
    pub struct KVid {
        DEBUG_FORMAT = "$k{}",
    }
}

newtype_index! {
    pub struct Name {
        DEBUG_FORMAT = "a{}",
        const NAME0 = 0,
        const NAME1 = 1,
        const NAME2 = 2,
    }
}

impl<Tag> Constraint<Tag> {
    pub const TRUE: Self = Self::Pred(Pred::Expr(Expr::Constant(Constant::Bool(true))), None);
}

impl BinOp {
    pub fn precedence(&self) -> Precedence {
        match self {
            BinOp::Iff => Precedence::Iff,
            BinOp::Imp => Precedence::Imp,
            BinOp::Or => Precedence::Or,
            BinOp::And => Precedence::And,
            BinOp::Eq | BinOp::Ne | BinOp::Gt | BinOp::Lt | BinOp::Ge | BinOp::Le => {
                Precedence::Cmp
            }
            BinOp::Add | BinOp::Sub => Precedence::AddSub,
            BinOp::Mul | BinOp::Div | BinOp::Mod => Precedence::MulDiv,
        }
    }
}

impl Precedence {
    pub fn is_associative(&self) -> bool {
        !matches!(self, Precedence::Imp | Precedence::Cmp)
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
                write!(f, "(and")?;
                write!(PadAdapter::wrap_fmt(f, 2), "{}", preds.iter().join("\n"))?;
                write!(f, "\n)")
            }
            Constraint::Guard(body, head) => {
                write!(f, "(forall ((_ Unit) ({body}))")?;
                write!(PadAdapter::wrap_fmt(f, 2), "\n{head}")?;
                write!(f, "\n)")
            }
            Constraint::ForAll(x, sort, body, head) => {
                write!(f, "(forall (({x:?} {sort}) {body})")?;
                write!(PadAdapter::wrap_fmt(f, 2), "\n{}", head)?;
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
                if let [pred] = &preds[..] {
                    write!(f, "{}", PredTag(pred, tag))
                } else {
                    write!(f, "(and")?;
                    let mut w = PadAdapter::wrap_fmt(f, 2);
                    for pred in preds {
                        write!(w, "\n{}", PredTag(pred, tag))?;
                    }
                    write!(f, "\n)")
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
            Sort::Unit => write!(f, "Unit"),
            Sort::Pair(s1, s2) => write!(f, "(Pair {s1} {s2})"),
        }
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
                if let [pred] = &preds[..] {
                    write!(f, "{}", pred)
                } else {
                    write!(f, "(and {})", preds.iter().join(" "))
                }
            }
            Pred::KVar(kvid, vars) => {
                write!(f, "({:?} {:?})", kvid, vars.iter().format(" "))
            }
            Pred::Expr(expr) => write!(f, "({})", expr),
        }
    }
}

impl Expr {
    pub const ZERO: Expr = Expr::Constant(Constant::ZERO);
    pub const ONE: Expr = Expr::Constant(Constant::ONE);
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn should_parenthesize(op: BinOp, child: &Expr) -> bool {
            if let Expr::BinaryOp(child_op, ..) = child {
                child_op.precedence() < op.precedence()
                    || (child_op.precedence() == op.precedence()
                        && !op.precedence().is_associative())
            } else {
                false
            }
        }

        match self {
            Expr::Var(x) => write!(f, "{:?}", x),
            Expr::Constant(c) => write!(f, "{}", c),
            Expr::BinaryOp(op, e1, e2) => {
                if should_parenthesize(*op, e1) {
                    write!(f, "({})", e1)?;
                } else {
                    write!(f, "{}", e1)?;
                }
                write!(f, " {} ", op)?;
                if should_parenthesize(*op, e2) {
                    write!(f, "({})", e2)?;
                } else {
                    write!(f, "{}", e2)?;
                }
                Ok(())
            }
            Expr::UnaryOp(op, e) => {
                if matches!(e.as_ref(), Expr::Constant(_) | Expr::Var(_)) {
                    write!(f, "{}{}", op, e)
                } else {
                    write!(f, "{}({})", op, e)
                }
            }
            Expr::Pair(e1, e2) => write!(f, "(Pair ({e1}) ({e2}))"),
            Expr::Proj(e, Proj::Fst) => write!(f, "(fst {e})"),
            Expr::Proj(e, Proj::Snd) => write!(f, "(snd {e})"),
            Expr::Unit => write!(f, "Unit"),
        }
    }
}

pub(crate) static DEFAULT_QUALIFIERS: SyncLazy<Vec<Qualifier>> = SyncLazy::new(|| {
    // Unary

    // (qualif EqZero ((v int)) (v == 0))
    let eqzero = Qualifier {
        args: vec![(NAME0, Sort::Int)],
        expr: Expr::BinaryOp(BinOp::Eq, Box::new(Expr::Var(NAME0)), Box::new(Expr::ZERO)),
        name: String::from("EqZero"),
    };

    // (qualif GtZero ((v int)) (v > 0))
    let gtzero = Qualifier {
        args: vec![(NAME0, Sort::Int)],
        expr: Expr::BinaryOp(BinOp::Gt, Box::new(Expr::Var(NAME0)), Box::new(Expr::ZERO)),
        name: String::from("GtZero"),
    };

    // (qualif GeZero ((v int)) (v >= 0))
    let gezero = Qualifier {
        args: vec![(NAME0, Sort::Int)],
        expr: Expr::BinaryOp(BinOp::Ge, Box::new(Expr::Var(NAME0)), Box::new(Expr::ZERO)),
        name: String::from("GeZero"),
    };

    // (qualif LtZero ((v int)) (v < 0))
    let ltzero = Qualifier {
        args: vec![(NAME0, Sort::Int)],
        expr: Expr::BinaryOp(BinOp::Lt, Box::new(Expr::Var(NAME0)), Box::new(Expr::ZERO)),
        name: String::from("LtZero"),
    };

    // (qualif LeZero ((v int)) (v <= 0))
    let lezero = Qualifier {
        args: vec![(NAME0, Sort::Int)],
        expr: Expr::BinaryOp(BinOp::Le, Box::new(Expr::Var(NAME0)), Box::new(Expr::ZERO)),
        name: String::from("LeZero"),
    };

    // Binary

    // (qualif Eq ((a int) (b int)) (a == b))
    let eq = Qualifier {
        args: vec![(NAME0, Sort::Int), (NAME1, Sort::Int)],
        expr: Expr::BinaryOp(BinOp::Eq, Box::new(Expr::Var(NAME0)), Box::new(Expr::Var(NAME1))),
        name: String::from("Eq"),
    };

    // (qualif Gt ((a int) (b int)) (a > b))
    let gt = Qualifier {
        args: vec![(NAME0, Sort::Int), (NAME1, Sort::Int)],
        expr: Expr::BinaryOp(BinOp::Gt, Box::new(Expr::Var(NAME0)), Box::new(Expr::Var(NAME1))),
        name: String::from("Gt"),
    };

    // (qualif Lt ((a int) (b int)) (a < b))
    let ge = Qualifier {
        args: vec![(NAME0, Sort::Int), (NAME1, Sort::Int)],
        expr: Expr::BinaryOp(BinOp::Ge, Box::new(Expr::Var(NAME0)), Box::new(Expr::Var(NAME1))),
        name: String::from("Ge"),
    };

    // (qualif Ge ((a int) (b int)) (a >= b))
    let lt = Qualifier {
        args: vec![(NAME0, Sort::Int), (NAME1, Sort::Int)],
        expr: Expr::BinaryOp(BinOp::Lt, Box::new(Expr::Var(NAME0)), Box::new(Expr::Var(NAME1))),
        name: String::from("Lt"),
    };

    // (qualif Le ((a int) (b int)) (a <= b))
    let le = Qualifier {
        args: vec![(NAME0, Sort::Int), (NAME1, Sort::Int)],
        expr: Expr::BinaryOp(BinOp::Le, Box::new(Expr::Var(NAME0)), Box::new(Expr::Var(NAME1))),
        name: String::from("Le"),
    };

    // (qualif Le1 ((a int) (b int)) (a < b - 1))
    let le1 = Qualifier {
        args: vec![(NAME0, Sort::Int), (NAME1, Sort::Int)],
        expr: Expr::BinaryOp(
            BinOp::Le,
            Box::new(Expr::Var(NAME0)),
            Box::new(Expr::BinaryOp(BinOp::Sub, Box::new(Expr::Var(NAME1)), Box::new(Expr::ONE))),
        ),
        name: String::from("Le1"),
    };

    // (qualif Add2 ((a int) (b int) (c int)) (a == b + c))
    let add2 = Qualifier {
        args: vec![(NAME0, Sort::Int), (NAME1, Sort::Int), (NAME2, Sort::Int)],
        expr: Expr::BinaryOp(
            BinOp::Eq,
            Box::new(Expr::Var(NAME0)),
            Box::new(Expr::BinaryOp(BinOp::Add, Box::new(Expr::Var(NAME1)), Box::new(Expr::Var(NAME2)))),
        ),
        name: String::from("Add2"),
    };


    // (qualif Sub2 ((a int) (b int) (c int)) (a == b - c))
    let sub2 = Qualifier {
        args: vec![(NAME0, Sort::Int), (NAME1, Sort::Int), (NAME2, Sort::Int)],
        expr: Expr::BinaryOp(
            BinOp::Eq,
            Box::new(Expr::Var(NAME0)),
            Box::new(Expr::BinaryOp(BinOp::Sub, Box::new(Expr::Var(NAME1)), Box::new(Expr::Var(NAME2)))),
        ),
        name: String::from("Sub2"),
    };


    vec![eqzero, gtzero, gezero, ltzero, lezero, eq, gt, ge, lt, le, le1, add2, sub2]
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
            self.expr
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

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constant::Int(Sign::Positive, n) => write!(f, "{}", n),
            Constant::Int(Sign::Negative, n) => write!(f, "-{}", n),
            Constant::Bool(b) => write!(f, "{}", b),
        }
    }
}

impl Constant {
    pub const ZERO: Constant = Constant::Int(Sign::Positive, 0);
    pub const ONE: Constant = Constant::Int(Sign::Positive, 1);
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
