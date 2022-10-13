use std::{collections::HashMap, sync::LazyLock};

use flux_middle::{
    rustc::mir,
    ty::{BinOp, Expr},
};
use rustc_span::Span;

use crate::constraint_gen::Tag;

pub enum Pre {
    None,
    Some(fn(Span) -> Tag, fn(Expr, Expr) -> Expr),
}

pub struct ArithSig {
    pub pre: Pre,
    pub out: Output,
}

#[derive(Copy, Clone)]
pub enum Output {
    Indexed(fn(Expr, Expr) -> Expr),
    Exists(fn(Expr, Expr, Expr) -> Expr),
}

pub fn unsigned_arith(op: mir::BinOp) -> &'static ArithSig {
    &UNSIGNED_ARITH_SIGS[&op]
}

pub fn signed_arith(op: mir::BinOp) -> &'static ArithSig {
    &SIGNED_ARITH_SIGS[&op]
}

macro_rules! output {
    (|$a:ident, $b: ident| $out:expr) => {
        Output::Indexed(|$a, $b| $out)
    };
    (|$a:ident, $b: ident| .{$v:ident : $out:expr}) => {
        Output::Exists(|$v, $a, $b| $out)
    };
}

macro_rules! arith {
    (|$a:ident, $b:ident| $tag:ident : $pre:expr  => $($out:tt)*) => {{
        use flux_middle::ty::Expr;
        use crate::constraint_gen::Tag;
        #[allow(unused_variables)]
        let pre: fn(Expr, Expr) -> Expr = |$a: Expr, $b: Expr| $pre;
        let out = output!(|$a, $b| $($out)*) ;
        ArithSig { pre: Pre::Some(Tag::$tag, pre), out }
    }};
    (|$a:ident, $b:ident| .none => $($out:tt)*) => {{
        #[allow(unused_variables)]
        let out = output!(|$a, $b| $($out)*) ;
        ArithSig { pre: Pre::None, out }
    }};
}

type E = Expr;

type ArithSigs = HashMap<mir::BinOp, ArithSig>;

static UNSIGNED_ARITH_SIGS: LazyLock<ArithSigs> = LazyLock::new(|| {
    use mir::BinOp::*;
    HashMap::from([
        (Add, arith!(|a, b| Overflow: E::ge(a + b, 0) => a + b)),
        (Sub, arith!(|a, b| Overflow: E::ge(a - b, 0) => a - b)),
        (Div, arith!(|a, b|      Div: E::ne(b, 0)     => a / b)),
        (Rem, arith!(|a, b|      Rem: E::ne(b, 0)     => E::binary_op(BinOp::Mod, a, b))),
        (Mul, arith!(|a, b| .none  => a * b)),
    ])
});

#[rustfmt::skip]
static SIGNED_ARITH_SIGS: LazyLock<ArithSigs> = LazyLock::new(|| {
    use mir::BinOp::*;
    HashMap::from([
        (Add, arith!(|a, b| .none => a + b)),
        (Sub, arith!(|a, b| .none => a - b)),
        (Mul, arith!(|a, b| .none => a * b)),
        (Div, arith!(|a, b| Div: E::ne(b, 0) => a / b)),
        (Rem, arith!(|a, b| Rem: E::ne(b, 0) => .{ v : E::implies(
                                                         E::and([E::ge(&a, 0), E::ge(&b, 0)]),
                                                         E::eq(v, E::binary_op(BinOp::Mod, a, b))) }),
        ),
    ])
});
