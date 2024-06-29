use std::{hash::Hash, sync::LazyLock};

use flux_macros::signatures;
use flux_middle::{
    rty::{self, BaseTy, Expr},
    rustc::mir,
};
use rty::{BinOp::Mod, Expr as E};
use rustc_data_structures::unord::UnordMap;

use crate::constraint_gen::ConstrReason;

pub(crate) struct PrimOpSig<const N: usize> {
    pub pre: Pre<N>,
    pub out: Output<N>,
}

pub(crate) enum Pre<const N: usize> {
    None,
    Some(ConstrReason, Box<dyn Fn([Expr; N]) -> Expr + Sync + Send>),
}

pub(crate) enum Output<const N: usize> {
    Base(BaseTy),
    Indexed(BaseTy, fn([Expr; N]) -> Expr),
    Exists(BaseTy, fn(Expr, [Expr; N]) -> Expr),
}

pub(crate) fn get_bin_op_sig(
    op: mir::BinOp,
    bty1: &BaseTy,
    bty2: &BaseTy,
    check_overflow: bool,
) -> PrimOpSig<2> {
    let table = if check_overflow { &OVERFLOW_BIN_OPS } else { &DEFAULT_BIN_OPS };
    table.get(&op, [bty1.clone(), bty2.clone()])
}

pub(crate) fn get_un_op_sig(op: mir::UnOp, bty: &BaseTy, check_overflow: bool) -> PrimOpSig<1> {
    let table = if check_overflow { &OVERFLOW_UN_OPS } else { &DEFAULT_UN_OPS };
    table.get(&op, [bty.clone()])
}

impl<const N: usize> Output<N> {
    pub(crate) fn to_ty(&self, exprs: [Expr; N]) -> rty::Ty {
        match self {
            Output::Indexed(bty, mk) => rty::Ty::indexed(bty.clone(), mk(exprs)),
            Output::Exists(bty, mk) => {
                rty::Ty::exists_with_constr(bty.clone(), mk(Expr::nu(), exprs))
            }
            Output::Base(bty) => bty.to_ty(),
        }
    }
}

struct Table<K: Eq + Hash, const N: usize> {
    factories: UnordMap<K, PrimOpFactory<N>>,
}

impl<K: Eq + Hash, const N: usize> Table<K, N> {
    fn get(&self, k: &K, inputs: [BaseTy; N]) -> PrimOpSig<N> {
        let factory = &self.factories[&k];
        (factory.make)(&inputs).unwrap()
    }
}

struct PrimOpFactory<const N: usize> {
    make: fn(&[BaseTy; N]) -> Option<PrimOpSig<N>>,
}

static DEFAULT_BIN_OPS: LazyLock<Table<mir::BinOp, 2>> = LazyLock::new(|| {
    use mir::BinOp::*;
    Table {
        factories: [
            // Arith
            (Add, mk_add_sigs(false)),
            (Mul, mk_mul_sigs(false)),
            (Sub, mk_sub_sigs(false)),
            (Div, mk_div_sigs()),
            (Rem, mk_rem_sigs()),
            // Logic
            (BitAnd, mk_bit_and_sigs()),
            (BitOr, mk_bit_or_sigs()),
            // Cmp
            (Eq, mk_eq_sigs()),
            (Ne, mk_ne_sigs()),
            (Le, mk_le_sigs()),
            (Ge, mk_ge_sigs()),
            (Lt, mk_lt_sigs()),
            (Gt, mk_gt_sigs()),
            // Shifts
            (Shl, mk_shl_sigs()),
            (Shr, mk_shr_sigs()),
        ]
        .into_iter()
        .collect(),
    }
});

static OVERFLOW_BIN_OPS: LazyLock<Table<mir::BinOp, 2>> = LazyLock::new(|| {
    use mir::BinOp::*;
    Table {
        factories: [
            // Arith
            (Add, mk_add_sigs(true)),
            (Mul, mk_mul_sigs(true)),
            (Sub, mk_sub_sigs(true)),
            (Div, mk_div_sigs()),
            (Rem, mk_rem_sigs()),
            // Bitwise
            (BitAnd, mk_bit_and_sigs()),
            (BitOr, mk_bit_or_sigs()),
            // Cmp
            (Eq, mk_eq_sigs()),
            (Ne, mk_ne_sigs()),
            (Le, mk_le_sigs()),
            (Ge, mk_ge_sigs()),
            (Lt, mk_lt_sigs()),
            (Gt, mk_gt_sigs()),
            // Shifts
            (Shl, mk_shl_sigs()),
            (Shr, mk_shr_sigs()),
        ]
        .into_iter()
        .collect(),
    }
});

static DEFAULT_UN_OPS: LazyLock<Table<mir::UnOp, 1>> = LazyLock::new(|| {
    use mir::UnOp::*;
    Table {
        factories: [(Neg, mk_neg_sigs(false)), (Not, mk_not_sigs())]
            .into_iter()
            .collect(),
    }
});

static OVERFLOW_UN_OPS: LazyLock<Table<mir::UnOp, 1>> = LazyLock::new(|| {
    use mir::UnOp::*;
    Table {
        factories: [(Neg, mk_neg_sigs(true)), (Not, mk_not_sigs())]
            .into_iter()
            .collect(),
    }
});

/// `a + b`
fn mk_add_sigs(check_overflow: bool) -> PrimOpFactory<2> {
    if check_overflow {
        signatures! {
            fn(a: T, b: T) -> T[a + b]
            requires E::and([
                         E::ge(&a + &b, E::int_min(int_ty)),
                         E::le(a + b, E::int_max(int_ty)),
                     ]) => ConstrReason::Overflow
            if let &BaseTy::Int(int_ty) = T

            fn(a: T, b: T) -> T[a + b]
            requires E::le(a + b, E::uint_max(uint_ty)) => ConstrReason::Overflow
            if let &BaseTy::Uint(uint_ty) = T

            fn(a: T, b: T) -> T
        }
    } else {
        signatures! {
            fn(a: T, b: T) -> T[a + b]
            if T.is_integral()

            fn(a: T, b: T) -> T
        }
    }
}

/// `a * b`
fn mk_mul_sigs(check_overflow: bool) -> PrimOpFactory<2> {
    if check_overflow {
        signatures! {
            fn(a: T, b: T) -> T[a * b]
            requires E::and([
                         E::ge(&a * &b, E::int_min(int_ty)),
                         E::le(a * b, E::int_max(int_ty)),
                     ]) => ConstrReason::Overflow
            if let &BaseTy::Int(int_ty) = T

            fn(a: T, b: T) -> T[a * b]
            requires E::le(a * b, E::uint_max(uint_ty)) => ConstrReason::Overflow
            if let &BaseTy::Uint(uint_ty) = T

            fn(a: T, b: T) -> T
        }
    } else {
        signatures!(
            fn(a: T, b: T) -> T[a * b]
            if T.is_integral()

            fn(a: T, b: T) -> T
            if T.is_float()
        )
    }
}

/// `a - b`
fn mk_sub_sigs(check_overflow: bool) -> PrimOpFactory<2> {
    if check_overflow {
        signatures! {
            fn(a: T, b: T) -> T[a - b]
            requires E::and([
                         E::ge(&a - &b, E::int_min(int_ty)),
                         E::le(a - b, E::int_max(int_ty)),
                     ]) => ConstrReason::Overflow
            if let &BaseTy::Int(int_ty) = T

            fn(a: T, b: T) -> T[a - b]
            requires E::and([
                         E::ge(&a - &b, 0),
                         E::le(a - b, E::uint_max(uint_ty)),
                     ]) => ConstrReason::Overflow
            if let &BaseTy::Uint(uint_ty) = T

            fn(a: T, b: T) -> T
        }
    } else {
        signatures! {
            fn(a: T, b: T) -> T[a - b]
            requires E::ge(a - b, 0) => ConstrReason::Overflow
            if T.is_unsigned()

            fn(a: T, b: T) -> T[a - b]
            if T.is_signed()

            fn(a: T, b: T) -> T
            if T.is_float()
        }
    }
}

/// `a/b`
fn mk_div_sigs() -> PrimOpFactory<2> {
    signatures! {
        fn(a: T, b: T) -> T[a/b]
        requires E::ne(b, 0) => ConstrReason::Div
        if T.is_integral()

        fn(a: T, b: T) -> T
        if T.is_float()
    }
}

/// `a % b`
fn mk_rem_sigs() -> PrimOpFactory<2> {
    signatures! {
        fn(a: T, b: T) -> T[E::binary_op(Mod, a, b, None)]
        requires E::ne(b, 0) => ConstrReason::Rem
        if T.is_unsigned()

        fn(a: T, b: T) -> T{v: E::implies(
                                   E::and([E::ge(&a, 0), E::ge(&b, 0)]),
                                   E::eq(v, E::binary_op(Mod, a, b, None))) }
        requires E::ne(b, 0) => ConstrReason::Rem
        if T.is_signed()
    }
}

/// `a & b`
fn mk_bit_and_sigs() -> PrimOpFactory<2> {
    signatures! {
        fn(a: T, b: T) -> T{v: E::tt()}
        if T.is_integral()

        fn(a: bool, b: bool) -> bool[E::and([a, b])]
    }
}

/// `a | b`
fn mk_bit_or_sigs() -> PrimOpFactory<2> {
    signatures! {
        fn(a: T, b: T) -> T{v: E::tt()}
        if T.is_integral()

        fn(a: bool, b: bool) -> bool[E::or([a, b])]
    }
}

/// `a == b`
fn mk_eq_sigs() -> PrimOpFactory<2> {
    signatures! {
        fn(a: T, b: T) -> bool[E::eq(a, b)]
        if T.is_integral() || T.is_bool()

        fn(a: T, b: T) -> bool
    }
}

/// `a != b`
fn mk_ne_sigs() -> PrimOpFactory<2> {
    signatures! {
        fn(a: T, b: T) -> bool[E::ne(a, b)]
        if T.is_integral() || T.is_bool()

        fn(a: T, b: T) -> bool
    }
}

/// `a <= b`
fn mk_le_sigs() -> PrimOpFactory<2> {
    signatures! {
        fn(a: T, b: T) -> bool[E::le(a, b)]
        if T.is_integral()

        fn(a: bool, b: bool) -> bool[E::implies(a, b)]

        fn(a: T, b: T) -> bool
    }
}

/// `a >= b`
fn mk_ge_sigs() -> PrimOpFactory<2> {
    signatures! {
        fn(a: T, b: T) -> bool[E::ge(a, b)]
        if T.is_integral()

        fn(a: bool, b: bool) -> bool[E::implies(b, a)]

        fn(a: T, b: T) -> bool
    }
}

/// `a < b`
fn mk_lt_sigs() -> PrimOpFactory<2> {
    signatures! {
        fn(a: T, b: T) -> bool[E::lt(a, b)]
        if T.is_integral()

        fn(a: bool, b: bool) -> bool[E::and([a.not(), b])]

        fn(a: T, b: T) -> bool
    }
}

/// `a > b`
fn mk_gt_sigs() -> PrimOpFactory<2> {
    signatures! {
        fn(a: T, b: T) -> bool[E::gt(a, b)]
        if T.is_integral()

        fn(a: bool, b: bool) -> bool[E::and([a, b.not()])]

        fn(a: T, b: T) -> bool
    }
}

/// `a << b`
fn mk_shl_sigs() -> PrimOpFactory<2> {
    signatures! {
        fn(a: T, b: S) -> T
        if T.is_integral() && S.is_integral()
    }
}

/// `a >> b`
fn mk_shr_sigs() -> PrimOpFactory<2> {
    signatures! {
        fn(a: T, b: S) -> T
        if T.is_integral() && S.is_integral()
    }
}

/// `-a`
fn mk_neg_sigs(check_overflow: bool) -> PrimOpFactory<1> {
    if check_overflow {
        signatures! {
            fn(a: T) -> T[a.neg()]
            requires E::ne(a, E::int_min(int_ty)) => ConstrReason::Overflow
            if let &BaseTy::Int(int_ty) = T
        }
    } else {
        signatures! {
            fn(a: T) -> T[a.neg()]
            if T.is_integral()

            fn(a: T) -> T
            if T.is_float()
        }
    }
}

/// `!a`
fn mk_not_sigs() -> PrimOpFactory<1> {
    signatures! {
        fn(a: bool) -> bool[a.not()]

        fn(a: T) -> T
        if T.is_integral()
    }
}
