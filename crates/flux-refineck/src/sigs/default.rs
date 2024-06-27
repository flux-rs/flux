use std::sync::LazyLock;

use flux_middle::{
    rty::{BaseTy, BinOp, Expr, INT_TYS, UINT_TYS},
    rustc::mir,
};
use itertools::{chain, iproduct};

use super::{Sig, SigTable};
use crate::{
    constraint_gen::ConstrReason,
    sigs::{define_btys, s},
};

type E = Expr;

pub(super) static BIN_OPS: LazyLock<SigTable<mir::BinOp, 2>> = LazyLock::new(|| {
    let mut table = SigTable::new();

    table.extend(mk_signed_bin_ops());
    table.extend(mk_unsigned_bin_ops());
    table.extend(mk_signed_shift_ops());
    table.extend(mk_unsigned_shift_ops());
    table.extend(mk_bool_bin_ops());

    table
});

pub(super) static UN_OPS: LazyLock<SigTable<mir::UnOp, 1>> = LazyLock::new(|| {
    let mut table = SigTable::new();

    table.extend(mk_neg());
    table.extend([mk_not()]);
    table.extend(mk_lnot());

    table
});

/// This set of signatures does not check for overflow. They check for underflow
/// in subtraction.
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
            [
                // ARITH
                (Add, s!(fn(a: Uint, b: Uint) -> Uint[a + b])),
                (Mul, s!(fn(a: Uint, b: Uint) -> Uint[a * b])),
                (Sub, s!(fn(a: Uint, b: Uint) -> Uint[a - b]
                         requires E::ge(a - b, 0) => ConstrReason::Overflow)
                ),
                (Div, s!(fn(a: Uint, b: Uint) -> Uint[a / b]
                         requires E::ne(b, 0) => ConstrReason::Div),
                ),
                (Rem, s!(fn(a:Uint , b: Uint) -> Uint[E::binary_op(BinOp::Mod, a, b, None)]
                         requires E::ne(b, 0) => ConstrReason::Rem),
                ),
                // BIT
                (BitAnd, s!(fn(a: Uint, b: Uint) -> Uint{v: E::tt()})),
                (BitOr,  s!(fn(a: Uint, b: Uint) -> Uint{v: E::tt()})),
                (BitXor, s!(fn(a: Uint, b: Uint) -> Uint{v: E::tt()})),
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
            [
                // ARITH
                (Add, s!(fn(a: Int, b: Int) -> Int[a + b])),
                (Sub, s!(fn(a: Int, b: Int) -> Int[a - b])),
                (Mul, s!(fn(a: Int, b: Int) -> Int[a * b])),
                (Div, s!(fn(a: Int, b: Int) -> Int[a / b]
                            requires E::ne(b, 0) => ConstrReason::Div),
                ),
                (Rem, s!(fn(a:Int , b: Int) -> Int{v: E::implies(
                                                          E::and([E::ge(&a, 0), E::ge(&b, 0)]),
                                                          E::eq(v, E::binary_op(BinOp::Mod, a, b, None))) }
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

#[rustfmt::skip]
pub(crate) fn mk_bool_bin_ops() -> impl IntoIterator<Item = (mir::BinOp, Sig<2>)> {
    use mir::BinOp::*;
    define_btys! { let bool = BaseTy::Bool; }
    [
        // BIT
        (BitAnd, s!(fn(a: bool, b: bool) -> bool[E::and([a, b])])),
        (BitOr, s!(fn(a: bool, b: bool) -> bool[E::or([a, b])])),
        // CMP
        (Eq, s!(fn(a: bool, b: bool) -> bool[E::eq(a, b)])),
        (Ne, s!(fn(a: bool, b: bool) -> bool[E::ne(a, b)])),
        (Le, s!(fn(a: bool, b: bool) -> bool[E::implies(a, b)])),
        (Ge, s!(fn(a: bool, b: bool) -> bool[E::implies(b, a)])),
        (Lt, s!(fn(a: bool, b: bool) -> bool[E::and([a.not(), b])])),
        (Gt, s!(fn(a: bool, b: bool) -> bool[E::and([a, b.not()])])),
    ]
}

#[rustfmt::skip]
pub(crate) fn mk_signed_shift_ops() -> impl IntoIterator<Item = (mir::BinOp, Sig<2>)> {
    use mir::BinOp::*;
    iproduct!(INT_TYS, UINT_TYS)
        .flat_map(|(int_ty, uint_ty)|{
            define_btys! {
                let Int = BaseTy::Int(int_ty);
                let Uint = BaseTy::Uint(uint_ty);
            }
            [
                (Shl, s!(fn(a: Int, b: Int) -> Int{ v: E::tt() })),
                (Shl, s!(fn(a: Int, b: Uint) -> Int{ v: E::tt() })),
                (Shr, s!(fn(a: Int, b: Int) -> Int{ v: E::tt() })),
                (Shr, s!(fn(a: Int, b: Uint) -> Int{ v: E::tt() })),

                (Shl, s!(fn(a: Uint, b: Int) -> Uint{ v: E::tt() })),
                (Shl, s!(fn(a: Uint, b: Uint) -> Uint{ v: E::tt() })),
                (Shr, s!(fn(a: Uint, b: Int) -> Uint{ v: E::tt() })),
                (Shr, s!(fn(a: Uint, b: Uint) -> Uint{ v: E::tt() })),
            ]
        })
}

#[rustfmt::skip]
pub(crate) fn mk_unsigned_shift_ops() -> impl IntoIterator<Item = (mir::BinOp, Sig<2>)> {
    use mir::BinOp::*;
    iproduct!(UINT_TYS, UINT_TYS)
        .flat_map(|(uint_ty_l, uint_ty_r)|{
            define_btys! {
                let Int = BaseTy::Uint(uint_ty_l);
                let Uint = BaseTy::Uint(uint_ty_r);
            }
            [
                (Shl, s!(fn(a: Int, b: Int) -> Int{ v: E::tt() })),
                (Shl, s!(fn(a: Int, b: Uint) -> Int{ v: E::tt() })),
                (Shr, s!(fn(a: Int, b: Int) -> Int{ v: E::tt() })),
                (Shr, s!(fn(a: Int, b: Uint) -> Int{ v: E::tt() })),

                (Shl, s!(fn(a: Uint, b: Int) -> Uint{ v: E::tt() })),
                (Shl, s!(fn(a: Uint, b: Uint) -> Uint{ v: E::tt() })),
                (Shr, s!(fn(a: Uint, b: Int) -> Uint{ v: E::tt() })),
                (Shr, s!(fn(a: Uint, b: Uint) -> Uint{ v: E::tt() })),
            ]
        })
}

#[rustfmt::skip]
fn mk_neg() -> impl Iterator<Item = (mir::UnOp, Sig<1>)> {
    use mir::UnOp::*;
    INT_TYS
        .into_iter()
        .map(|int_ty| {
            define_btys! { let Int = BaseTy::Int(int_ty); }
            (Neg, s!(fn(a: Int) -> Int[a.neg()]))
        })
}

pub(crate) fn mk_not() -> (mir::UnOp, Sig<1>) {
    define_btys! { let bool = BaseTy::Bool; }
    (mir::UnOp::Not, s!(fn(a: bool) -> bool[a.not()]))
}

pub(crate) fn mk_lnot() -> impl IntoIterator<Item = (mir::UnOp, Sig<1>)> {
    let int_lnots = INT_TYS.map(|int_ty| {
        define_btys! { let Int = BaseTy::Int(int_ty); };
        (mir::UnOp::Not, s!(fn(a: Int) -> Int{v: E::tt()}))
    });

    let uint_lnots = UINT_TYS.map(|uint_ty| {
        define_btys! { let Uint = BaseTy::Uint(uint_ty); };
        (mir::UnOp::Not, s!(fn(a: Uint) -> Uint{v: E::tt()}))
    });

    chain!(int_lnots, uint_lnots)
}
