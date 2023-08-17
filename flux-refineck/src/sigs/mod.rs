mod default;
mod overflow;

use flux_middle::{
    rty::{self, BaseTy, Expr},
    rustc::mir,
};
use rustc_hash::FxHashMap;

use crate::constraint_gen::ConstrReason;

pub(crate) struct Sig<const N: usize> {
    pub args: [BaseTy; N],
    pub pre: Pre<N>,
    pub out: Output<N>,
}

pub(crate) enum Pre<const N: usize> {
    None,
    Some(ConstrReason, Box<dyn Fn([Expr; N]) -> Expr + Sync + Send>),
}

pub(crate) enum Output<const N: usize> {
    Indexed(BaseTy, fn([Expr; N]) -> Expr),
    Exists(BaseTy, fn(Expr, [Expr; N]) -> Expr),
}

struct SigTable<T, const N: usize> {
    map: FxHashMap<(T, [BaseTy; N]), Sig<N>>,
}

pub(crate) fn get_bin_op_sig(
    op: mir::BinOp,
    bty1: &BaseTy,
    bty2: &BaseTy,
    check_overflow: bool,
) -> &'static Sig<2> {
    let table = if check_overflow { &overflow::BIN_OPS } else { &default::BIN_OPS };
    table.get(op, [bty1.clone(), bty2.clone()])
}

pub(crate) fn get_un_op_sig(op: mir::UnOp, bty: &BaseTy, check_overflow: bool) -> &'static Sig<1> {
    let table = if check_overflow { &overflow::UN_OPS } else { &default::UN_OPS };
    table.get(op, [bty.clone()])
}

impl<const N: usize> Output<N> {
    pub(crate) fn to_ty(&self, exprs: [Expr; N]) -> rty::Ty {
        match self {
            Output::Indexed(bty, mk) => rty::Ty::indexed(bty.clone(), mk(exprs)),
            Output::Exists(bty, mk) => {
                rty::Ty::exists_with_constr(bty.clone(), mk(Expr::nu(), exprs))
            }
        }
    }
}

#[macro_export]
macro_rules! _define_btys {
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
use crate::_define_btys as define_btys;

#[macro_export]
macro_rules! _sig {
    (fn ($($arg:ident:$ty:ident),+) -> $($rest:tt)+) => {{
        let (pre, out) = s!(($($arg),+) $($rest)+) ;
        let args = [$(bty!($ty)),+];
        $crate::sigs::Sig { args, pre, out }
    }};
    (($($args:ident),+) $bty:ident[$out:expr] $($rest:tt)*) => {{
        let bty = bty!($bty);
        #[allow(unused_variables)]
        let pre = s!(($($args),+) $($rest)*);
        #[allow(unused_variables)]
        let out = $crate::sigs::Output::Indexed(bty, |[$($args),+]| $out);
        (pre, out)
    }};
    (($($args:ident),+) $bty:ident{$v:ident : $out:expr} $($rest:tt)*) => {{
        let bty = bty!($bty);
        #[allow(unused_variables)]
        let pre = s!(($($args),+) $($rest)*);
        #[allow(unused_variables)]
        let out = $crate::sigs::Output::Exists(bty, |$v, [$($args),+]| $out);
        (pre, out)
    }};
    (($($args:ident),+)) => {
        $crate::sigs::Pre::None
    };
    (($($args:ident),+) requires $pre:expr => $tag:path) => {
        $crate::sigs::Pre::Some($tag, Box::new(move |[$($args),+]| $pre))
    };
}
use crate::_sig as s;

impl<T, const N: usize> SigTable<T, N> {
    fn new() -> Self {
        Self { map: FxHashMap::default() }
    }
}

impl<T, const N: usize> SigTable<T, N>
where
    T: std::hash::Hash + Eq + std::fmt::Debug,
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
