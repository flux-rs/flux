use std::{
    cell::RefCell,
    fmt::{self, Write},
};

use itertools::{Format, Itertools};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use crate::{
    intern::{Internable, Interned},
    ty::{BaseTy, BinOp, ExprKind, ExprS, ParamTy, Pred, RegionS, Ty, TyKind, TyS, UnOp, Var},
    tyenv::{RegionKind, TyEnv},
};

#[macro_export]
macro_rules! _define_scoped {
    ($cx:ident, $fmt:expr) => {
        #[allow(unused_macros)]
        macro_rules! scoped_cx {
            () => {
                $cx
            };
        }

        #[allow(unused_macros)]
        macro_rules! scoped_fmt {
            () => {
                $fmt
            };
        }
    };
}
pub use crate::_define_scoped as define_scoped;

#[macro_export]
macro_rules! _with_cx {
    ($e:expr) => {
        $crate::pretty::WithCx::new(scoped_cx!(), $e)
    };
}
pub use crate::_with_cx as with_cx;

#[macro_export]
macro_rules! _format_args_cx {
    ($fmt:literal, $($args:tt)*) => {
        format_args_cx!(@go ($fmt; $($args)*) -> ())
    };
    ($fmt:literal) => {
        format_args!($fmt)
    };
    (@go ($fmt:literal; ^$head:expr, $($tail:tt)*) -> ($($accum:tt)*)) => {
        format_args_cx!(@go ($fmt; $($tail)*) -> ($($accum)* $head,))
    };
    (@go ($fmt:literal; $head:expr, $($tail:tt)*) -> ($($accum:tt)*)) => {
        format_args_cx!(@go ($fmt; $($tail)*) -> ($($accum)* $crate::pretty::with_cx!($head),))
    };
    (@go ($fmt:literal; ^$head:expr) -> ($($accum:tt)*)) => {
        format_args_cx!(@as_expr format_args!($fmt, $($accum)* $head,))
    };
    (@go ($fmt:literal; $head:expr) -> ($($accum:tt)*)) => {
        format_args_cx!(@as_expr format_args!($fmt, $($accum)* $crate::pretty::with_cx!($head),))
    };
    (@as_expr $e:expr) => { $e };
}
pub use crate::_format_args_cx as format_args_cx;

#[macro_export]
macro_rules! _w {
    ($fmt:literal, $($args:tt)*) => {
        scoped_fmt!().write_fmt(format_args_cx!($fmt, $($args)*))
    };
    ($fmt:literal) => {
        write!(scoped_fmt!(), $fmt)
    }
}
pub use crate::_w as w;

#[macro_export]
macro_rules! _join {
    ($sep:expr, $iter:expr) => {
        $crate::pretty::Join::new($sep, $iter.into_iter())
    };
}
pub use crate::_join as join;

#[macro_export]
macro_rules! _impl_debug_with_default_cx {
    ($($ty:ty),* $(,)?) => {$(
        impl fmt::Debug for $ty  {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                rustc_middle::ty::tls::with(|tcx| {
                    let cx = <$ty>::default_cx(tcx);
                    Pretty::fmt(self, &cx, f)
                })
            }
        }
    )*};
}
pub use crate::_impl_debug_with_default_cx as impl_debug_with_default_cx;

pub enum Visibility {
    Hide,
    Show,
    Ellipsis,
}
pub struct PPrintCx<'tcx> {
    tcx: TyCtxt<'tcx>,
    vars_in_scope: Visibility,
    fully_qualified_paths: bool,
    nu: Visibility,
}

pub struct WithCx<'a, 'tcx, T> {
    data: T,
    cx: &'a PPrintCx<'tcx>,
}

pub struct Join<'a, I> {
    sep: &'a str,
    iter: RefCell<Option<I>>,
}

pub trait Pretty {
    fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result;

    fn default_cx(tcx: TyCtxt) -> PPrintCx {
        PPrintCx::default(tcx)
    }
}

impl<'a, I> Join<'a, I> {
    pub fn new(sep: &'a str, iter: I) -> Self {
        Self {
            sep,
            iter: RefCell::new(Some(iter)),
        }
    }
}

impl Visibility {
    /// Returns `true` if the visibility is [`Hide`].
    ///
    /// [`Hide`]: Visibility::Hide
    pub fn is_hide(&self) -> bool {
        matches!(self, Self::Hide)
    }
}

impl PPrintCx<'_> {
    pub fn default(tcx: TyCtxt) -> PPrintCx {
        PPrintCx {
            tcx,
            vars_in_scope: Visibility::Show,
            nu: Visibility::Show,
            fully_qualified_paths: false,
        }
    }

    pub fn vars_in_scope(self, vis: Visibility) -> Self {
        Self {
            vars_in_scope: vis,
            ..self
        }
    }

    pub fn nu(self, vis: Visibility) -> Self {
        Self { nu: vis, ..self }
    }

    pub fn fully_qualified_paths(self, b: bool) -> Self {
        Self {
            fully_qualified_paths: b,
            ..self
        }
    }
}

impl<'a, 'tcx, T> WithCx<'a, 'tcx, T> {
    pub fn new(cx: &'a PPrintCx<'tcx>, data: T) -> Self {
        Self { data, cx }
    }
}

impl<T: Pretty + ?Sized> Pretty for &'_ T {
    fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <T as Pretty>::fmt(self, cx, f)
    }
}

impl<T: Pretty + Internable> Pretty for Interned<T> {
    fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <T as Pretty>::fmt(self, cx, f)
    }
}

impl<T, I> fmt::Debug for Join<'_, I>
where
    T: fmt::Debug,
    I: Iterator<Item = T>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut iter = match self.iter.borrow_mut().take() {
            Some(t) => t,
            None => panic!("Join: was already formatted once"),
        };
        for (i, item) in iter.enumerate() {
            if i > 0 {
                write!(f, "{}", self.sep)?;
            }
            <T as fmt::Debug>::fmt(&item, f)?;
        }
        Ok(())
    }
}

impl<T, I> Pretty for Join<'_, I>
where
    T: Pretty,
    I: Iterator<Item = T>,
{
    fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut iter = match self.iter.borrow_mut().take() {
            Some(t) => t,
            None => panic!("Join: was already formatted once"),
        };
        for (i, item) in iter.enumerate() {
            if i > 0 {
                write!(f, "{}", self.sep)?;
            }
            <T as Pretty>::fmt(&item, cx, f)?;
        }
        Ok(())
    }
}

impl<T: Pretty> fmt::Debug for WithCx<'_, '_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <T as Pretty>::fmt(&self.data, self.cx, f)
    }
}

impl Pretty for TyEnv {
    fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        let bindings = self
            .iter()
            .filter(|(_, binding)| !binding.ty().is_uninit())
            .map(|(set, elem)| (set.sorted().collect_vec(), elem))
            .sorted_by(|(set1, _), (set2, _)| set1.cmp(set2))
            .collect_vec();

        w!("{{");
        for (i, (set, binding)) in bindings.into_iter().enumerate() {
            if i > 0 {
                w!(", ");
            }
            match set[..] {
                [idx] => {
                    w!("{:?}: ", ^idx)?;
                }
                _ => {
                    w!("{{{:?}}}: ", ^join!(", ", set))?;
                }
            }
            w!("{:?}", binding)?;
        }
        w!("}}")
    }

    fn default_cx(tcx: TyCtxt) -> PPrintCx {
        PPrintCx::default(tcx)
            .vars_in_scope(Visibility::Hide)
            .nu(Visibility::Hide)
    }
}

impl Pretty for TyS {
    fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        match self.kind() {
            TyKind::Refine(bty, e) => {
                if matches!(e.kind(), ExprKind::Constant(..) | ExprKind::Var(..)) {
                    w!("{:?}@{:?}", bty, e)
                } else {
                    w!("{:?}@{{{:?}}}", bty, e)
                }
            }
            TyKind::Exists(bty, p) => w!("{:?}{{{:?}}}", bty, p),
            TyKind::Uninit => w!("uninit"),
            TyKind::MutRef(region) => w!("ref<{:?}>", region),
            TyKind::Param(ParamTy { name, .. }) => w!("{:?}", ^name),
        }
    }

    fn default_cx(tcx: TyCtxt) -> PPrintCx {
        PPrintCx::default(tcx).vars_in_scope(Visibility::Ellipsis)
    }
}

impl Pretty for BaseTy {
    fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        match self {
            BaseTy::Int(int_ty) => write!(f, "{}", int_ty.name_str()),
            BaseTy::Uint(uint_ty) => write!(f, "{}", uint_ty.name_str()),
            BaseTy::Bool => w!("bool"),
            BaseTy::Adt(did, args) => {
                w!("{:?}", did)?;
                if !args.is_empty() {
                    w!("<{:?}>", join!(", ", args));
                }
                Ok(())
            }
        }
    }
}

impl Pretty for DefId {
    fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let path = cx.tcx.def_path(*self);
        if cx.fully_qualified_paths {
            let krate = cx.tcx.crate_name(self.krate);
            write!(f, "{krate}{}", path.to_string_no_crate_verbose())
        } else {
            write!(f, "{}", path.data.last().unwrap())
        }
    }
}

impl Pretty for Pred {
    fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        match self {
            Self::KVar(kvid, e, args) => {
                w!("{:?}", ^kvid)?;
                if !cx.nu.is_hide() || !cx.vars_in_scope.is_hide() {
                    w!("(")?;
                    match cx.nu {
                        Visibility::Show => w!("{:?}", e)?,
                        Visibility::Ellipsis => w!("…")?,
                        Visibility::Hide => {}
                    }
                    match cx.vars_in_scope {
                        Visibility::Show => w!(", {:?}", join!(", ", args))?,
                        Visibility::Ellipsis => w!(", …")?,
                        Visibility::Hide => {}
                    }
                    w!(")")?;
                }
                Ok(())
            }
            Self::Expr(expr) => w!("{:?}", expr),
        }
    }

    fn default_cx(tcx: TyCtxt) -> PPrintCx {
        PPrintCx::default(tcx).fully_qualified_paths(true)
    }
}

impl Pretty for ExprS {
    fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        fn should_parenthesize(op: BinOp, child: &ExprS) -> bool {
            if let ExprKind::BinaryOp(child_op, ..) = child.kind() {
                child_op.precedence() < op.precedence()
                    || (child_op.precedence() == op.precedence()
                        && !op.precedence().is_associative())
            } else {
                false
            }
        }

        match self.kind() {
            ExprKind::Var(x) => w!("{:?}", ^x),
            ExprKind::BinaryOp(op, e1, e2) => {
                if should_parenthesize(*op, e1) {
                    w!("({:?})", e1)?;
                } else {
                    w!("{:?}", e1)?;
                }
                w!(" {:?} ", op)?;
                if should_parenthesize(*op, e2) {
                    w!("({:?})", e2)?;
                } else {
                    w!("{:?}", e2)?;
                }
                Ok(())
            }
            ExprKind::Constant(c) => w!("{}", ^c),
            ExprKind::UnaryOp(UnOp::Not, e) => match e.kind() {
                ExprKind::UnaryOp(UnOp::Not, e) => w!("{:?}", e),
                ExprKind::BinaryOp(BinOp::Eq, e1, e2) => {
                    let e = ExprKind::BinaryOp(BinOp::Ne, e1.clone(), e2.clone()).intern();
                    w!("{:?}", e)
                }
                ExprKind::Var(_) | ExprKind::Constant(_) => {
                    w!("{:?}{:?}", UnOp::Not, e)
                }
                _ => {
                    w!("{:?}({:?})", UnOp::Not, e)
                }
            },
            ExprKind::UnaryOp(op, e) => {
                if matches!(e.kind(), ExprKind::Var(_) | ExprKind::Constant(_)) {
                    w!("{:?}{:?}", op, e)
                } else {
                    w!("{:?}({:?})", op, e)
                }
            }
        }
    }
}

impl Pretty for BinOp {
    fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        match self {
            BinOp::Iff => w!("⇔"),
            BinOp::Imp => w!("⇒"),
            BinOp::Or => w!("∨"),
            BinOp::And => w!("∧"),
            BinOp::Eq => w!("="),
            BinOp::Ne => w!("≠"),
            BinOp::Gt => w!(">"),
            BinOp::Ge => w!("≥"),
            BinOp::Lt => w!("<"),
            BinOp::Le => w!("≤"),
            BinOp::Add => w!("+"),
            BinOp::Sub => w!("-"),
        }
    }
}

impl Pretty for UnOp {
    fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        match self {
            UnOp::Not => w!("¬"),
            UnOp::Neg => w!("-"),
        }
    }
}

impl Pretty for Var {
    fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        match self {
            Var::Bound => w!("ν"),
            Var::Free(var) => w!("{:?}", ^var),
        }
    }
}

impl Pretty for RegionS {
    fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        if self.len() == 1 {
            w!("{:?}", ^self[0])
        } else {
            w!("{{{:?}}}", ^join!(",", self))
        }
    }
}

impl Pretty for RegionKind {
    fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        define_scoped!(cx, f);
        match self {
            RegionKind::Strong(ty) => w!("{:?}", ty),
            RegionKind::Weak { bound, ty } => {
                w!("{:?} <: {:?}", ty, bound)
            }
        }
    }
}

impl_debug_with_default_cx!(TyEnv, TyS, BaseTy, Pred, ExprS, Var, RegionS, RegionKind);
