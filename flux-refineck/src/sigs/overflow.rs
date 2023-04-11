use std::sync::LazyLock;

use flux_middle::{
    rty::{BaseTy, BinOp, Expr},
    rustc::mir,
};

use super::{Sig, SigTable};
use crate::{
    constraint_gen::ConstrReason,
    sigs::{define_btys, s, INT_TYS, UINT_TYS},
};

type E = Expr;

pub(super) static BIN_OPS: LazyLock<SigTable<mir::BinOp, 2>> = LazyLock::new(|| {
    let mut table = SigTable::new();

    table.extend(mk_signed_bin_ops());
    table.extend(mk_unsigned_bin_ops());
    table.extend(super::default::mk_shift_ops());
    table.extend(super::default::mk_bool_bin_ops());

    table
});

/// This set of signatures checks for overflow and underflow. They work in
/// tandem with the invariant for unsigned ints returned in
/// [`BaseTy::invariants`].
///
/// [`BaseTy::invariants`]: flux_middle::rty::BaseTy::invariants
#[rustfmt::skip]
fn mk_unsigned_bin_ops() -> impl Iterator<Item = (mir::BinOp, Sig<2>)> {
    use mir::BinOp::*;
    UINT_TYS
        .into_iter()
        .flat_map(|uint_ty| {
            define_btys! {
                let bool = BaseTy::Bool;
                let Uint = BaseTy::Uint(uint_ty);
            }
            let bit_width: u64 = uint_ty.bit_width().unwrap_or(flux_config::pointer_width().bits());
            [
                // ARITH
                (Add, s!(fn(a: Uint, b: Uint) -> Uint[a + b]
                         requires E::le(a + b, E::uint_max(bit_width)) => ConstrReason::Overflow)
                ),
                (Mul, s!(fn(a: Uint, b: Uint) -> Uint[a * b]
                         requires E::le(a * b, E::uint_max(bit_width)) => ConstrReason::Overflow)
                ),
                (Sub, s!(fn(a: Uint, b: Uint) -> Uint[a - b]
                         requires E::ge(a - b, 0) => ConstrReason::Overflow)
                ),
                (Div, s!(fn(a: Uint, b: Uint) -> Uint[a / b]
                         requires E::ne(b, 0) => ConstrReason::Div),
                ),
                (Rem, s!(fn(a:Uint , b: Uint) -> Uint[E::binary_op(BinOp::Mod, a, b)]
                         requires E::ne(b, 0) => ConstrReason::Rem),
                ),
                // BIT
                (BitAnd, s!(fn(a: Uint, b: Uint) -> Uint{v: E::tt()})),
                (BitOr,  s!(fn(a: Uint, b: Uint) -> Uint{v: E::tt()})),
                // CMP
                (Eq, s!(fn(a: Uint, b: Uint) -> bool[E::eq(a, b)])),
                (Ne, s!(fn(a: Uint, b: Uint) -> bool[E::ne(a, b)])),
                (Le, s!(fn(a: Uint, b: Uint) -> bool[E::le(a, b)])),
                (Ge, s!(fn(a: Uint, b: Uint) -> bool[E::ge(a, b)])),
                (Lt, s!(fn(a: Uint, b: Uint) -> bool[E::lt(a, b)])),
                (Gt, s!(fn(a: Uint, b: Uint) -> bool[E::gt(a, b)])),
            ]
        })
}

#[rustfmt::skip]
fn mk_signed_bin_ops() -> impl Iterator<Item = (mir::BinOp, Sig<2>)> {
    use mir::BinOp::*;
    INT_TYS
        .into_iter()
        .flat_map(|int_ty| {
            define_btys! {
                let bool = BaseTy::Bool;
                let Int = BaseTy::Int(int_ty);
            }
            let bit_width: u64 = int_ty.bit_width().unwrap_or(flux_config::pointer_width().bits());
            [
                // ARITH
                (Add, s!(fn(a: Int, b: Int) -> Int[a + b]
                            requires E::and([
                                         E::le(&a + &b, E::int_max(bit_width)),
                                         E::ge(a + b, E::int_min(bit_width))
                                     ]) => ConstrReason::Overflow)
                ),
                (Sub, s!(fn(a: Int, b: Int) -> Int[a - b]
                            requires E::and([
                                         E::le(&a - &b, E::int_max(bit_width)),
                                         E::ge(a - b, E::int_min(bit_width))
                                     ]) => ConstrReason::Overflow)
                ),
                (Mul, s!(fn(a: Int, b: Int) -> Int[a * b]
                            requires E::and([
                                         E::le(&a - &b, E::int_max(bit_width)),
                                         E::ge(a - b, E::int_min(bit_width))
                                     ]) => ConstrReason::Overflow)
                ),
                (Div, s!(fn(a: Int, b: Int) -> Int[a / b]
                            requires E::ne(b, 0) => ConstrReason::Div),
                ),
                (Rem, s!(fn(a:Int , b: Int) -> Int{v: E::implies(
                                                          E::and([E::ge(&a, 0), E::ge(&b, 0)]),
                                                          E::eq(v, E::binary_op(BinOp::Mod, a, b))) }
                            requires E::ne(b, 0) => ConstrReason::Rem),
                ),
                // BIT
                (BitAnd, s!(fn(a: Int, b: Int) -> Int{v: E::tt()})),
                (BitOr,  s!(fn(a: Int, b: Int) -> Int{v: E::tt()})),
                // CMP
                (Eq, s!(fn(a: Int, b: Int) -> bool[E::eq(a, b)])),
                (Ne, s!(fn(a: Int, b: Int) -> bool[E::ne(a, b)])),
                (Le, s!(fn(a: Int, b: Int) -> bool[E::le(a, b)])),
                (Ge, s!(fn(a: Int, b: Int) -> bool[E::ge(a, b)])),
                (Lt, s!(fn(a: Int, b: Int) -> bool[E::lt(a, b)])),
                (Gt, s!(fn(a: Int, b: Int) -> bool[E::gt(a, b)])),
            ]
        })
}
