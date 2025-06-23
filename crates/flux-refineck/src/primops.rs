/// This file defines the refinement rules for primitive operations.
/// Flux needs to define how to reason about primitive operations on different
/// [`BaseTy`]s. This is done by defining a set of rules for each operation.
///
/// For example, equality checks depend on whether the `BaseTy` is treated as
/// refineable or opaque.
///
/// ```
/// // Make the rules for `a == b`.
/// fn mk_eq_rules() -> RuleMatcher<2> {
///     primop_rules! {
///         // if the `BaseTy` is refineable, then we can reason about equality.
///         // The specified types in the `if` are refineable and Flux will use
///         // the refined postcondition (`bool[E::eq(a, b)]`) to reason about
///         // the invariants of `==`.
///         fn(a: T, b: T) -> bool[E::eq(a, b)]
///         if T.is_integral() || T.is_bool() || T.is_char() || T.is_str()
///
///         // Otherwise, if the `BaseTy` is opaque, then we can't reason
///         // about equality. Flux only knows that the return type is a boolean,
///         // but the return value is unrefined.
///         fn(a: T, b: T) -> bool
///     }
/// }
/// ```
use std::{fmt, hash::Hash, sync::LazyLock};

use flux_common::tracked_span_bug;
use flux_infer::infer::ConstrReason;
use flux_macros::primop_rules;
use flux_middle::rty::{self, BaseTy, Expr, Sort};
use flux_rustc_bridge::mir;
use rty::{BinOp::Mod, Expr as E};
use rustc_data_structures::unord::UnordMap;

#[derive(Debug)]
pub(crate) struct MatchedRule {
    pub precondition: Option<Pre>,
    pub output_type: rty::Ty,
}

#[derive(Debug)]
pub(crate) struct Pre {
    pub reason: ConstrReason,
    pub pred: Expr,
}

pub(crate) fn match_bin_op(
    op: mir::BinOp,
    bty1: &BaseTy,
    idx1: &Expr,
    bty2: &BaseTy,
    idx2: &Expr,
    check_overflow: bool,
) -> MatchedRule {
    let table = if check_overflow { &OVERFLOW_BIN_OPS } else { &DEFAULT_BIN_OPS };
    table.match_inputs(&op, [(bty1.clone(), idx1.clone()), (bty2.clone(), idx2.clone())])
}

pub(crate) fn match_un_op(
    op: mir::UnOp,
    bty: &BaseTy,
    idx: &Expr,
    check_overflow: bool,
) -> MatchedRule {
    let table = if check_overflow { &OVERFLOW_UN_OPS } else { &DEFAULT_UN_OPS };
    table.match_inputs(&op, [(bty.clone(), idx.clone())])
}

struct RuleTable<Op: Eq + Hash, const N: usize> {
    rules: UnordMap<Op, RuleMatcher<N>>,
}

impl<Op: Eq + Hash + fmt::Debug, const N: usize> RuleTable<Op, N> {
    fn match_inputs(&self, op: &Op, inputs: [(BaseTy, Expr); N]) -> MatchedRule {
        (self.rules[op])(&inputs)
            .unwrap_or_else(|| tracked_span_bug!("no primop rule for {op:?} using {inputs:?}"))
    }
}

type RuleMatcher<const N: usize> = fn(&[(BaseTy, Expr); N]) -> Option<MatchedRule>;

static DEFAULT_BIN_OPS: LazyLock<RuleTable<mir::BinOp, 2>> = LazyLock::new(|| {
    use mir::BinOp::*;
    RuleTable {
        rules: [
            // Arith
            (Add, mk_add_rules(false)),
            (Mul, mk_mul_rules(false)),
            (Sub, mk_sub_rules(false)),
            (Div, mk_div_rules()),
            (Rem, mk_rem_rules()),
            // Bitwise
            (BitAnd, mk_bit_and_rules()),
            (BitOr, mk_bit_or_rules()),
            (BitXor, mk_bit_xor_rules()),
            // Cmp
            (Eq, mk_eq_rules()),
            (Ne, mk_ne_rules()),
            (Le, mk_le_rules()),
            (Ge, mk_ge_rules()),
            (Lt, mk_lt_rules()),
            (Gt, mk_gt_rules()),
            // Shifts
            (Shl, mk_shl_rules()),
            (Shr, mk_shr_rules()),
        ]
        .into_iter()
        .collect(),
    }
});

static OVERFLOW_BIN_OPS: LazyLock<RuleTable<mir::BinOp, 2>> = LazyLock::new(|| {
    use mir::BinOp::*;
    RuleTable {
        rules: [
            // Arith
            (Add, mk_add_rules(true)),
            (Mul, mk_mul_rules(true)),
            (Sub, mk_sub_rules(true)),
            (Div, mk_div_rules()),
            (Rem, mk_rem_rules()),
            // Bitwise
            (BitAnd, mk_bit_and_rules()),
            (BitOr, mk_bit_or_rules()),
            (BitXor, mk_bit_xor_rules()),
            // Cmp
            (Eq, mk_eq_rules()),
            (Ne, mk_ne_rules()),
            (Le, mk_le_rules()),
            (Ge, mk_ge_rules()),
            (Lt, mk_lt_rules()),
            (Gt, mk_gt_rules()),
            // Shifts
            (Shl, mk_shl_rules()),
            (Shr, mk_shr_rules()),
        ]
        .into_iter()
        .collect(),
    }
});

static DEFAULT_UN_OPS: LazyLock<RuleTable<mir::UnOp, 1>> = LazyLock::new(|| {
    use mir::UnOp::*;
    RuleTable {
        rules: [(Neg, mk_neg_rules(false)), (Not, mk_not_rules())]
            .into_iter()
            .collect(),
    }
});

static OVERFLOW_UN_OPS: LazyLock<RuleTable<mir::UnOp, 1>> = LazyLock::new(|| {
    use mir::UnOp::*;
    RuleTable {
        rules: [(Neg, mk_neg_rules(true)), (Not, mk_not_rules())]
            .into_iter()
            .collect(),
    }
});

/// `a + b`
fn mk_add_rules(check_overflow: bool) -> RuleMatcher<2> {
    if check_overflow {
        primop_rules! {
            fn(a: T, b: T) -> T[a + b]
            requires E::and(
                         E::ge(a + b, E::int_min(int_ty)),
                         E::le(a + b, E::int_max(int_ty)),
                     ) => ConstrReason::Overflow
            if let &BaseTy::Int(int_ty) = T

            fn(a: T, b: T) -> T[a + b]
            requires E::le(a + b, E::uint_max(uint_ty)) => ConstrReason::Overflow
            if let &BaseTy::Uint(uint_ty) = T

            fn(a: T, b: T) -> T
        }
    } else {
        primop_rules! {
            fn(a: T, b: T) -> T[a + b]
            if T.is_integral()

            fn(a: T, b: T) -> T
        }
    }
}

/// `a * b`
fn mk_mul_rules(check_overflow: bool) -> RuleMatcher<2> {
    if check_overflow {
        primop_rules! {
            fn(a: T, b: T) -> T[a * b]
            requires E::and(
                         E::ge(a * b, E::int_min(int_ty)),
                         E::le(a * b, E::int_max(int_ty)),
                     ) => ConstrReason::Overflow
            if let &BaseTy::Int(int_ty) = T

            fn(a: T, b: T) -> T[a * b]
            requires E::le(a * b, E::uint_max(uint_ty)) => ConstrReason::Overflow
            if let &BaseTy::Uint(uint_ty) = T

            fn(a: T, b: T) -> T
        }
    } else {
        primop_rules!(
            fn(a: T, b: T) -> T[a * b]
            if T.is_integral()

            fn(a: T, b: T) -> T
            if T.is_float()
        )
    }
}

/// `a - b`
fn mk_sub_rules(check_overflow: bool) -> RuleMatcher<2> {
    if check_overflow {
        primop_rules! {
            fn(a: T, b: T) -> T[a - b]
            requires E::and(
                         E::ge(a - b, E::int_min(int_ty)),
                         E::le(a - b, E::int_max(int_ty)),
                     ) => ConstrReason::Overflow
            if let &BaseTy::Int(int_ty) = T

            fn(a: T, b: T) -> T[a - b]
            requires E::and(
                         E::ge(a - b, 0),
                         E::le(a - b, E::uint_max(uint_ty)),
                     ) => ConstrReason::Overflow
            if let &BaseTy::Uint(uint_ty) = T

            fn(a: T, b: T) -> T
        }
    } else {
        primop_rules! {
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
fn mk_div_rules() -> RuleMatcher<2> {
    primop_rules! {
        fn(a: T, b: T) -> T[a/b]
        requires E::ne(b, 0) => ConstrReason::Div
        if T.is_integral()

        fn(a: T, b: T) -> T
        if T.is_float()
    }
}

/// `a % b`
fn mk_rem_rules() -> RuleMatcher<2> {
    primop_rules! {
        fn(a: T, b: T) -> T[E::binary_op(Mod(Sort::Int), a, b)]
        requires E::ne(b, 0) => ConstrReason::Rem
        if T.is_unsigned()

        fn(a: T, b: T) -> T{v: E::implies(
                                   E::and(E::ge(a, 0), E::ge(b, 0)),
                                   E::eq(v, E::binary_op(Mod(Sort::Int), a, b))) }
        requires E::ne(b, 0) => ConstrReason::Rem
        if T.is_signed()

        fn (a: T, b: T) -> T
        if T.is_float()
    }
}

/// `a & b`
fn mk_bit_and_rules() -> RuleMatcher<2> {
    primop_rules! {
        fn(a: T, b: T) -> T
        if T.is_integral()

        fn(a: bool, b: bool) -> bool[E::and(a, b)]
    }
}

/// `a | b`
fn mk_bit_or_rules() -> RuleMatcher<2> {
    primop_rules! {
        fn(a: T, b: T) -> T
        if T.is_integral()

        fn(a: bool, b: bool) -> bool[E::or(a, b)]
    }
}

/// `a ^ b`
fn mk_bit_xor_rules() -> RuleMatcher<2> {
    primop_rules! {
        fn(a: T, b: T) -> T
        if T.is_integral()
    }
}

/// `a == b`
fn mk_eq_rules() -> RuleMatcher<2> {
    primop_rules! {
        fn(a: T, b: T) -> bool[E::eq(a, b)]
        if T.is_integral() || T.is_bool() || T.is_char() || T.is_str()

        fn(a: T, b: T) -> bool
    }
}

/// `a != b`
fn mk_ne_rules() -> RuleMatcher<2> {
    primop_rules! {
        fn(a: T, b: T) -> bool[E::ne(a, b)]
        if T.is_integral() || T.is_bool()

        fn(a: T, b: T) -> bool
    }
}

/// `a <= b`
fn mk_le_rules() -> RuleMatcher<2> {
    primop_rules! {
        fn(a: T, b: T) -> bool[E::le(a, b)]
        if T.is_integral()

        fn(a: bool, b: bool) -> bool[E::implies(a, b)]

        fn(a: T, b: T) -> bool
    }
}

/// `a >= b`
fn mk_ge_rules() -> RuleMatcher<2> {
    primop_rules! {
        fn(a: T, b: T) -> bool[E::ge(a, b)]
        if T.is_integral()

        fn(a: bool, b: bool) -> bool[E::implies(b, a)]

        fn(a: T, b: T) -> bool
    }
}

/// `a < b`
fn mk_lt_rules() -> RuleMatcher<2> {
    primop_rules! {
        fn(a: T, b: T) -> bool[E::lt(a, b)]
        if T.is_integral()

        fn(a: bool, b: bool) -> bool[E::and(a.not(), b)]

        fn(a: T, b: T) -> bool
    }
}

/// `a > b`
fn mk_gt_rules() -> RuleMatcher<2> {
    primop_rules! {
        fn(a: T, b: T) -> bool[E::gt(a, b)]
        if T.is_integral()

        fn(a: bool, b: bool) -> bool[E::and(a, b.not())]

        fn(a: T, b: T) -> bool
    }
}

/// `a << b`
fn mk_shl_rules() -> RuleMatcher<2> {
    primop_rules! {
        fn(a: T, b: S) -> T[E::prim_val(rty::BinOp::BitShl, a, b)] [E::prim_rel(rty::BinOp::BitShl, a, b)]
        if T.is_integral() && S.is_integral()
    }
}

/// `a >> b`
fn mk_shr_rules() -> RuleMatcher<2> {
    primop_rules! {
        fn(a: T, b: S) -> T
        if T.is_integral() && S.is_integral()
    }
}

/// `-a`
fn mk_neg_rules(check_overflow: bool) -> RuleMatcher<1> {
    if check_overflow {
        primop_rules! {
            fn(a: T) -> T[a.neg()]
            requires E::ne(a, E::int_min(int_ty)) => ConstrReason::Overflow
            if let &BaseTy::Int(int_ty) = T

            fn(a: T) -> T[a.neg()]
            if T.is_float()
        }
    } else {
        primop_rules! {
            fn(a: T) -> T[a.neg()]
            if T.is_integral()

            fn(a: T) -> T
            if T.is_float()
        }
    }
}

/// `!a`
fn mk_not_rules() -> RuleMatcher<1> {
    primop_rules! {
        fn(a: bool) -> bool[a.not()]

        fn(a: T) -> T
        if T.is_integral()
    }
}
