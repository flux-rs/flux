use std::sync::LazyLock;

use flux_middle::{
    rty::{BaseTy, BinOp, Expr, IntTy, UintTy},
    rustc::mir,
};
use itertools::iproduct;
use rustc_hash::FxHashMap;

use crate::constraint_gen::ConstrReason;

#[derive(Clone)]
pub struct Sig<const N: usize> {
    pub args: [BaseTy; N],
    pub pre: Pre<N>,
    pub out: Output<N>,
}

#[derive(Copy, Clone)]
pub enum Pre<const N: usize> {
    None,
    Some(ConstrReason, fn([Expr; N]) -> Expr),
}

#[derive(Clone)]
pub enum Output<const N: usize> {
    Indexed(BaseTy, fn([Expr; N]) -> Expr),
    Exists(BaseTy, fn(Expr, [Expr; N]) -> Expr),
}

struct SigTable<T, const N: usize> {
    map: FxHashMap<(T, [BaseTy; N]), Sig<N>>,
}

pub fn get_bin_op_sig(op: mir::BinOp, bty1: &BaseTy, bty2: &BaseTy) -> &'static Sig<2> {
    BIN_OPS.get(op, [bty1.clone(), bty2.clone()])
}

type E = Expr;

macro_rules! define_btys {
    ($(let $name:ident = $bty:expr;)*) => {
        #[allow(unused_macros)]
        macro_rules! bty {
            $(
                ($name) => {
                    $bty
                };
            )*
        }
    };
}

macro_rules! s {
    (fn ($($arg:ident:$ty:ident),+) -> $($rest:tt)+) => {{
        let (pre, out) = s!(($($arg),+) $($rest)+) ;
        let args = [$(bty!($ty)),+];
        Sig { args, pre, out }
    }};
    (($($args:ident),+) $bty:ident[$out:expr] $($rest:tt)*) => {{
        let bty = bty!($bty);
        #[allow(unused_variables)]
        let pre = s!(($($args),+) $($rest)*);
        #[allow(unused_variables)]
        let out = Output::Indexed(bty, |[$($args),+]| $out);
        (pre, out)
    }};
    (($($args:ident),+) $bty:ident{$v:ident : $out:expr} $($rest:tt)*) => {{
        let bty = bty!($bty);
        #[allow(unused_variables)]
        let pre = s!(($($args),+) $($rest)*);
        #[allow(unused_variables)]
        let out = Output::Exists(bty, |$v, [$($args),+]| $out);
        (pre, out)
    }};
    (($($args:ident),+)) => {
        Pre::None
    };
    (($($args:ident),+) requires $pre:expr => $tag:path) => {
        Pre::Some($tag, |[$($args),+]| $pre)
    };
}

/// This set of signatures just checks subtraction does not underflow if
/// flux_config::check_overflow() = true and works in tandem with the invariant
/// for unsigned ints returned in [`BaseTy::invariants`].
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
            let sub = if flux_config::check_overflow() {
                (Sub, s!(fn(a: Uint, b: Uint) -> Uint[a - b]
                         requires E::ge(a - b, 0) => ConstrReason::Overflow)
                )
            } else {
                    (Sub, s!(fn(a: Uint, b: Uint) -> Uint[a - b]))
            };
            [
                // ARITH
                (Add, s!(fn(a: Uint, b: Uint) -> Uint[a + b])),
                (Mul, s!(fn(a: Uint, b: Uint) -> Uint[a * b])),
                sub,
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

#[rustfmt::skip]
fn mk_bool_bin_ops() -> impl IntoIterator<Item = (mir::BinOp, Sig<2>)> {
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
fn mk_shift_ops() -> impl IntoIterator<Item = (mir::BinOp, Sig<2>)> {
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

static BIN_OPS: LazyLock<SigTable<mir::BinOp, 2>> = LazyLock::new(|| {
    let mut table = SigTable::new();

    table.extend(mk_signed_bin_ops());
    table.extend(mk_unsigned_bin_ops());
    table.extend(mk_shift_ops());
    table.extend(mk_bool_bin_ops());

    table
});

impl<T, const N: usize> SigTable<T, N> {
    fn new() -> Self {
        Self { map: FxHashMap::default() }
    }
}

impl<T, const N: usize> SigTable<T, N>
where
    T: std::hash::Hash + Eq,
{
    fn extend(&mut self, iter: impl IntoIterator<Item = (T, Sig<N>)>) {
        self.map.extend(
            iter.into_iter()
                .map(|(op, sig)| ((op, sig.args.clone()), sig)),
        );
    }

    fn get(&self, op: T, btys: [BaseTy; N]) -> &Sig<N> {
        &self.map[&(op, btys)]
    }
}

static INT_TYS: [IntTy; 6] =
    [IntTy::Isize, IntTy::I8, IntTy::I16, IntTy::I32, IntTy::I64, IntTy::I128];
static UINT_TYS: [UintTy; 6] =
    [UintTy::Usize, UintTy::U8, UintTy::U16, UintTy::U32, UintTy::U64, UintTy::U128];
