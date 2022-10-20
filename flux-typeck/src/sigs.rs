use std::{collections::HashMap, sync::LazyLock};

use flux_middle::{
    rty::{BinOp, Expr},
    rustc::mir,
};
use rustc_span::Span;

use crate::constraint_gen::Tag;

#[derive(Copy, Clone)]
pub struct Sig<const N: usize> {
    pub pre: Pre<N>,
    pub out: Output<N>,
}

#[derive(Copy, Clone)]
pub enum Pre<const N: usize> {
    None,
    Some(fn(Span) -> Tag, fn([Expr; N]) -> Expr),
}

#[derive(Copy, Clone)]
pub enum Output<const N: usize> {
    Indexed(fn([Expr; N]) -> Expr),
    Exists(fn(Expr, [Expr; N]) -> Expr),
}

pub fn unsigned_bin_ops(op: mir::BinOp) -> Sig<2> {
    UNSIGNED_BIN_OPS[&op]
}

pub fn signed_bin_ops(op: mir::BinOp) -> Sig<2> {
    SIGNED_BIN_OPS[&op]
}

pub fn bool_bin_ops(op: mir::BinOp) -> Sig<2> {
    BOOL_BIN_OPS[&op]
}

macro_rules! output {
    (|$($args:ident),+| v = $out:expr) => {
        Output::Indexed(|[$($args),+]| $out)
    };
    (|$($args:ident),+| {$v:ident : $out:expr}) => {
        Output::Exists(|$v, [$($args),+]| $out)
    };
}

macro_rules! f {
    (|$($args:ident),+| $tag:ident : $pre:expr  => $($out:tt)*) => {{
        use crate::constraint_gen::Tag;
        #[allow(unused_variables)]
        let out = output!(|$($args),+| $($out)*) ;
        #[allow(unused_variables)]
        Sig { pre: Pre::Some(Tag::$tag, |[$($args),+]| $pre), out }
    }};
    (|$($args:ident),+| $($out:tt)*) => {{
        #[allow(unused_variables)]
        let out = output!(|$($args),+| $($out)*) ;
        #[allow(unused_variables)]
        Sig { pre: Pre::None, out }
    }};
}

type E = Expr;

type Sigs<T, const N: usize> = HashMap<T, Sig<N>>;

/// This set of signatures just checks substraction does not underflow and works
/// in tandem with the invariant for unsigned ints returned in [`BaseTy::invariants`].
///
/// [`BaseTy::invariants`]: flux_middle::rty::BaseTy::invariants
#[rustfmt::skip]
static UNSIGNED_BIN_OPS: LazyLock<Sigs<mir::BinOp, 2>> = LazyLock::new(|| {
    use mir::BinOp::*;
    HashMap::from([
        // ARITH
        (Sub, f!(|a,b| Overflow: E::ge(a - b, 0) => v = a - b)),
        (Div, f!(|a,b|      Div: E::ne(b, 0)     => v = a / b)),
        (Rem, f!(|a,b|      Rem: E::ne(b, 0)     => v = E::binary_op(BinOp::Mod, a, b))),
        (Add,    f!(|a,b| v = a + b)),
        (Mul,    f!(|a,b| v = a * b)),
        (BitAnd, f!(|a,b| { v : E::tt() })),
        // CMP
        (Eq, f!(|a,b| v = E::eq(a, b))),
        (Ne, f!(|a,b| v = E::ne(a, b))),
        (Le, f!(|a,b| v = E::le(a, b))),
        (Ge, f!(|a,b| v = E::ge(a, b))),
        (Lt, f!(|a,b| v = E::lt(a, b))),
        (Gt, f!(|a,b| v = E::gt(a, b))),
    ])
});

#[rustfmt::skip]
static SIGNED_BIN_OPS: LazyLock<Sigs<mir::BinOp, 2>> = LazyLock::new(|| {
    use mir::BinOp::*;
    HashMap::from([
        // ARITH
        (Add, f!(|a,b| v = a + b)),
        (Sub, f!(|a,b| v = a - b)),
        (Mul, f!(|a,b| v = a * b)),
        (Div, f!(|a,b| Div: E::ne(b, 0) => v = a / b)),
        (Rem, f!(|a,b| Rem: E::ne(b, 0) => { v : E::implies(
                                                     E::and([E::ge(&a, 0), E::ge(&b, 0)]),
                                                     E::eq(v, E::binary_op(BinOp::Mod, a, b))) }),
        ),
        (BitAnd, f!(|a,b| { v : E::tt() })),
        // CMP
        (Eq, f!(|a,b| v = E::eq(a, b))),
        (Ne, f!(|a,b| v = E::ne(a, b))),
        (Le, f!(|a,b| v = E::le(a, b))),
        (Ge, f!(|a,b| v = E::ge(a, b))),
        (Lt, f!(|a,b| v = E::lt(a, b))),
        (Gt, f!(|a,b| v = E::gt(a, b))),
    ])
});

#[rustfmt::skip]
static BOOL_BIN_OPS: LazyLock<Sigs<mir::BinOp, 2>> = LazyLock::new(|| {
    use mir::BinOp::*;
    HashMap::from([
        (BitAnd, f!(|a,b| v = E::and([a, b]))),
        // CMP
        (Eq, f!(|a,b| v = E::eq(a, b))),
        (Ne, f!(|a,b| v = E::ne(a, b))),
        (Le, f!(|a,b| v = E::implies(a, b))),
        (Ge, f!(|a,b| v = E::implies(b, a))),
        (Lt, f!(|a,b| v = E::and([a.not(), b]))),
        (Gt, f!(|a,b| v = E::and([a, b.not()]))),
    ])
});
