use std::sync::LazyLock;

use derive_where::derive_where;

use crate::{DefaultTypes, Types};

pub(crate) static DEFAULT_QUALIFIERS: LazyLock<[Qualifier<DefaultTypes>; 11]> =
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

        [eqzero, gtzero, gezero, ltzero, lezero, eq, gt, ge, lt, le, le1]
    });

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

impl<T: Types> Constraint<T> {
    pub const TRUE: Self = Self::Pred(Pred::TRUE, None);

    pub fn foralls(bindings: Vec<Bind<T>>, c: Self) -> Self {
        bindings
            .into_iter()
            .rev()
            .fold(c, |c, bind| Constraint::ForAll(bind, Box::new(c)))
    }

    /// Returns true if the constraint has at least one concrete RHS ("head") predicates.
    /// If `!c.is_concrete` then `c` is trivially satisfiable and we can avoid calling fixpoint.
    pub fn is_concrete(&self) -> bool {
        match self {
            Constraint::Conj(cs) => cs.iter().any(Constraint::is_concrete),
            Constraint::ForAll(_, c) => c.is_concrete(),
            Constraint::Pred(p, _) => p.is_concrete() && !p.is_trivially_true(),
        }
    }
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
    BvSize(u32),
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

    pub(crate) fn peel_out_abs(&self) -> (usize, &Sort<T>) {
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

impl<T: Types> Pred<T> {
    pub const TRUE: Self = Pred::Expr(Expr::Constant(Constant::Boolean(true)));

    pub fn is_trivially_true(&self) -> bool {
        match self {
            Pred::Expr(Expr::Constant(Constant::Boolean(true))) => true,
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

impl<T: Types> From<Constant<T>> for Expr<T> {
    fn from(v: Constant<T>) -> Self {
        Self::Constant(v)
    }
}

impl<T: Types> Expr<T> {
    pub const fn int(val: u128) -> Expr<T> {
        Expr::Constant(Constant::Numeral(val))
    }

    pub fn eq(self, other: Self) -> Self {
        Expr::Atom(BinRel::Eq, Box::new([self, other]))
    }
}

#[derive_where(Hash)]
pub enum Constant<T: Types> {
    Numeral(u128),
    Decimal(T::Decimal),
    Boolean(bool),
    String(T::String),
    BitVec(u128, u32),
}

#[derive_where(Hash)]
pub struct Qualifier<T: Types> {
    pub name: String,
    pub args: Vec<(T::Var, Sort<T>)>,
    pub body: Expr<T>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}
