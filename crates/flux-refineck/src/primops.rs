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
use flux_config::OverflowMode;
use flux_infer::infer::ConstrReason;
use flux_macros::primop_rules;
use flux_middle::rty::{self, BaseTy, Expr, Sort};
use flux_rustc_bridge::mir;
use rty::{
    BinOp::{BitAnd, BitOr, BitShl, BitShr, BitXor, Mod},
    Expr as E,
};
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
    overflow_mode: OverflowMode,
) -> MatchedRule {
    let table = match overflow_mode {
        OverflowMode::Strict => &OVERFLOW_STRICT_BIN_OPS,
        OverflowMode::Lazy => &OVERFLOW_LAZY_BIN_OPS,
        OverflowMode::None => &OVERFLOW_NONE_BIN_OPS,
        OverflowMode::StrictUnder => &OVERFLOW_STRICT_UNDER_BIN_OPS,
    };
    table.match_inputs(&op, [(bty1.clone(), idx1.clone()), (bty2.clone(), idx2.clone())])
}

pub(crate) fn match_un_op(
    op: mir::UnOp,
    bty: &BaseTy,
    idx: &Expr,
    overflow_mode: OverflowMode,
) -> MatchedRule {
    let table = match overflow_mode {
        OverflowMode::Strict => &OVERFLOW_STRICT_UN_OPS,
        OverflowMode::None => &OVERFLOW_NONE_UN_OPS,
        OverflowMode::Lazy | OverflowMode::StrictUnder => &OVERFLOW_LAZY_UN_OPS,
    };
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

static OVERFLOW_NONE_BIN_OPS: LazyLock<RuleTable<mir::BinOp, 2>> = LazyLock::new(|| {
    use mir::BinOp::*;
    RuleTable {
        rules: [
            // Arith
            (Add, mk_add_rules(OverflowMode::None)),
            (Mul, mk_mul_rules(OverflowMode::None)),
            (Sub, mk_sub_rules(OverflowMode::None)),
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

static OVERFLOW_STRICT_BIN_OPS: LazyLock<RuleTable<mir::BinOp, 2>> = LazyLock::new(|| {
    use mir::BinOp::*;
    RuleTable {
        rules: [
            // Arith
            (Add, mk_add_rules(OverflowMode::Strict)),
            (Mul, mk_mul_rules(OverflowMode::Strict)),
            (Sub, mk_sub_rules(OverflowMode::Strict)),
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

static OVERFLOW_LAZY_BIN_OPS: LazyLock<RuleTable<mir::BinOp, 2>> = LazyLock::new(|| {
    use mir::BinOp::*;
    RuleTable {
        rules: [
            // Arith
            (Add, mk_add_rules(OverflowMode::Lazy)),
            (Mul, mk_mul_rules(OverflowMode::Lazy)),
            (Sub, mk_sub_rules(OverflowMode::Lazy)),
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

static OVERFLOW_STRICT_UNDER_BIN_OPS: LazyLock<RuleTable<mir::BinOp, 2>> = LazyLock::new(|| {
    use mir::BinOp::*;
    RuleTable {
        rules: [
            // Arith
            (Add, mk_add_rules(OverflowMode::StrictUnder)),
            (Mul, mk_mul_rules(OverflowMode::StrictUnder)),
            (Sub, mk_sub_rules(OverflowMode::StrictUnder)),
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

static OVERFLOW_NONE_UN_OPS: LazyLock<RuleTable<mir::UnOp, 1>> = LazyLock::new(|| {
    use mir::UnOp::*;
    RuleTable {
        rules: [(Neg, mk_neg_rules(OverflowMode::None)), (Not, mk_not_rules())]
            .into_iter()
            .collect(),
    }
});

static OVERFLOW_LAZY_UN_OPS: LazyLock<RuleTable<mir::UnOp, 1>> = LazyLock::new(|| {
    use mir::UnOp::*;
    RuleTable {
        rules: [(Neg, mk_neg_rules(OverflowMode::Lazy)), (Not, mk_not_rules())]
            .into_iter()
            .collect(),
    }
});

static OVERFLOW_STRICT_UN_OPS: LazyLock<RuleTable<mir::UnOp, 1>> = LazyLock::new(|| {
    use mir::UnOp::*;
    RuleTable {
        rules: [(Neg, mk_neg_rules(OverflowMode::Strict)), (Not, mk_not_rules())]
            .into_iter()
            .collect(),
    }
});

fn valid_int(e: impl Into<Expr>, int_ty: rty::IntTy) -> rty::Expr {
    let e1 = e.into();
    let e2 = e1.clone();
    E::and(E::ge(e1, E::int_min(int_ty)), E::le(e2, E::int_max(int_ty)))
}

fn valid_uint(e: impl Into<Expr>, uint_ty: rty::UintTy) -> rty::Expr {
    let e1 = e.into();
    let e2 = e1.clone();
    E::and(E::ge(e1, 0), E::le(e2, E::uint_max(uint_ty)))
}

/// `a + b`
fn mk_add_rules(overflow_mode: OverflowMode) -> RuleMatcher<2> {
    match overflow_mode {
        OverflowMode::Strict => {
            primop_rules! {
                fn(a: T, b: T) -> T[a + b]
                requires valid_int(a + b, int_ty) => ConstrReason::Overflow
                if let &BaseTy::Int(int_ty) = T

                fn(a: T, b: T) -> T[a + b]
                requires valid_uint(a + b, uint_ty) => ConstrReason::Overflow
                if let &BaseTy::Uint(uint_ty) = T

                fn(a: T, b: T) -> T
            }
        }

        OverflowMode::Lazy | OverflowMode::StrictUnder => {
            primop_rules! {
                fn(a: T, b: T) -> T{v: E::implies(valid_int(a + b, int_ty), E::eq(v, a+b)) }
                if let &BaseTy::Int(int_ty) = T

                fn(a: T, b: T) -> T{v: E::implies(valid_uint(a + b, uint_ty), E::eq(v, a+b)) }
                if let &BaseTy::Uint(uint_ty) = T

                fn(a: T, b: T) -> T
            }
        }

        OverflowMode::None => {
            primop_rules! {
                fn(a: T, b: T) -> T[a + b]
                if T.is_integral()

                fn(a: T, b: T) -> T
            }
        }
    }
}

/// `a * b`
fn mk_mul_rules(overflow_mode: OverflowMode) -> RuleMatcher<2> {
    match overflow_mode {
        OverflowMode::Strict => {
            primop_rules! {
                fn(a: T, b: T) -> T[a * b]
                requires valid_int(a * b, int_ty) => ConstrReason::Overflow
                if let &BaseTy::Int(int_ty) = T

                fn(a: T, b: T) -> T[a * b]
                requires valid_uint(a * b, uint_ty) => ConstrReason::Overflow
                if let &BaseTy::Uint(uint_ty) = T

                fn(a: T, b: T) -> T
            }
        }

        OverflowMode::Lazy | OverflowMode::StrictUnder => {
            primop_rules! {
                fn(a: T, b: T) -> T{v: E::implies(valid_int(a * b, int_ty), E::eq(v, a * b)) }
                if let &BaseTy::Int(int_ty) = T

                fn(a: T, b: T) -> T{v: E::implies(valid_uint(a * b, uint_ty), E::eq(v, a * b)) }
                if let &BaseTy::Uint(uint_ty) = T

                fn(a: T, b: T) -> T
            }
        }

        OverflowMode::None => {
            primop_rules!(
                fn(a: T, b: T) -> T[a * b]
                if T.is_integral()

                fn(a: T, b: T) -> T
                if T.is_float()
            )
        }
    }
}

/// `a - b`
fn mk_sub_rules(overflow_mode: OverflowMode) -> RuleMatcher<2> {
    match overflow_mode {
        OverflowMode::Strict => {
            primop_rules! {
                fn(a: T, b: T) -> T[a - b]
                requires valid_int(a - b, int_ty) => ConstrReason::Overflow
                if let &BaseTy::Int(int_ty) = T

                fn(a: T, b: T) -> T[a - b]
                requires valid_uint(a - b, uint_ty) => ConstrReason::Overflow
                if let &BaseTy::Uint(uint_ty) = T

                fn(a: T, b: T) -> T
            }
        }

        // like Lazy, but we also check for underflow on unsigned subtraction
        OverflowMode::StrictUnder => {
            primop_rules! {
                fn(a: T, b: T) -> T{v: E::implies(valid_int(a - b, int_ty), E::eq(v, a - b)) }
                if let &BaseTy::Int(int_ty) = T

                fn(a: T, b: T) -> T{v: E::implies(valid_uint(a - b, uint_ty), E::eq(v, a - b)) }
                requires E::ge(a - b, 0) => ConstrReason::Underflow
                if let &BaseTy::Uint(uint_ty) = T

                fn(a: T, b: T) -> T
            }
        }

        OverflowMode::Lazy => {
            primop_rules! {
                fn(a: T, b: T) -> T{v: E::implies(valid_int(a - b, int_ty), E::eq(v, a - b)) }
                if let &BaseTy::Int(int_ty) = T

                fn(a: T, b: T) -> T{v: E::implies(valid_uint(a - b, uint_ty), E::eq(v, a - b)) }
                if let &BaseTy::Uint(uint_ty) = T

                fn(a: T, b: T) -> T
            }
        }

        OverflowMode::None => {
            primop_rules! {
                fn(a: T, b: T) -> T[a - b]
                requires E::ge(a - b, 0) => ConstrReason::Underflow
                if T.is_unsigned()

                fn(a: T, b: T) -> T[a - b]
                if T.is_signed()

                fn(a: T, b: T) -> T
                if T.is_float()
            }
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
        fn(a: T, b: T) -> { T[E::prim_val(BitAnd(Sort::Int), a, b)] | E::prim_rel(BitAnd(Sort::Int), a, b) }
        if T.is_integral()

        fn(a: bool, b: bool) -> bool[E::and(a, b)]
    }
}

/// `a | b`
fn mk_bit_or_rules() -> RuleMatcher<2> {
    primop_rules! {
        fn(a: T, b: T) -> { T[E::prim_val(BitOr(Sort::Int), a, b)] | E::prim_rel(BitOr(Sort::Int), a, b) }
        if T.is_integral()

        fn(a: bool, b: bool) -> bool[E::or(a, b)]
    }
}

/// `a ^ b`
fn mk_bit_xor_rules() -> RuleMatcher<2> {
    primop_rules! {
        fn(a: T, b: T) -> { T[E::prim_val(BitXor(Sort::Int), a, b)] | E::prim_rel(BitXor(Sort::Int), a, b) }
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
        fn(a: T, b: S) -> { T[E::prim_val(BitShl(Sort::Int), a, b)] | E::prim_rel(BitShl(Sort::Int), a, b) }
        if T.is_integral() && S.is_integral()
    }
}

/// `a >> b`
fn mk_shr_rules() -> RuleMatcher<2> {
    primop_rules! {
        fn(a: T, b: S) -> { T[E::prim_val(BitShr(Sort::Int), a, b)] | E::prim_rel(BitShr(Sort::Int), a, b) }
        if T.is_integral() && S.is_integral()
    }
}

/// `-a`
fn mk_neg_rules(overflow_mode: OverflowMode) -> RuleMatcher<1> {
    match overflow_mode {
        OverflowMode::Strict => {
            primop_rules! {
                fn(a: T) -> T[a.neg()]
                requires E::ne(a, E::int_min(int_ty)) => ConstrReason::Overflow
                if let &BaseTy::Int(int_ty) = T

                fn(a: T) -> T[a.neg()]
                if T.is_float()
            }
        }
        OverflowMode::Lazy | OverflowMode::StrictUnder => {
            primop_rules! {
                fn(a: T) -> T{v: E::implies(E::ne(a, E::int_min(int_ty)), E::eq(v, a.neg())) }
                if let &BaseTy::Int(int_ty) = T

                fn(a: T) -> T[a.neg()]
                if T.is_float()
            }
        }
        OverflowMode::None => {
            primop_rules! {
                fn(a: T) -> T[a.neg()]
                if T.is_integral()

                fn(a: T) -> T
                if T.is_float()
            }
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
