use std::{cell::RefCell, fmt};

use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use crate::intern::{Internable, Interned};

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
    ($f:expr, $fmt:literal, $($args:tt)*) => {
        $f.write_fmt(format_args_cx!($fmt, $($args)*))
    };
    ($f:expr, $fmt:literal) => {
        $f.write_fmt(format_args_cx!($fmt))
    };
    ($fmt:literal) => {
        write!(scoped_fmt!(), $fmt)
    }
}
pub use crate::_w as w;

#[macro_export]
macro_rules! _join {
    ($sep:expr, $iter:expr) => {
        $crate::pretty::Join::new($sep, $iter)
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
    Show,
    Hide,
    Truncate(usize),
}

pub struct PPrintCx<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub kvar_args: Visibility,
    pub fully_qualified_paths: bool,
    pub simplify_exprs: bool,
    pub tags: bool,
    pub bindings_chain: bool,
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
    pub fn new<T: IntoIterator<IntoIter = I>>(sep: &'a str, iter: T) -> Self {
        Self { sep, iter: RefCell::new(Some(iter.into_iter())) }
    }
}

impl PPrintCx<'_> {
    pub fn default(tcx: TyCtxt) -> PPrintCx {
        PPrintCx {
            tcx,
            kvar_args: Visibility::Show,
            fully_qualified_paths: false,
            simplify_exprs: true,
            tags: false,
            bindings_chain: true,
        }
    }

    pub fn kvar_args(self, kvar_args: Visibility) -> Self {
        Self { kvar_args, ..self }
    }

    pub fn fully_qualified_paths(self, b: bool) -> Self {
        Self { fully_qualified_paths: b, ..self }
    }

    #[allow(unused)]
    pub fn tags(self, tags: bool) -> Self {
        Self { tags, ..self }
    }

    #[allow(unused)]
    pub fn bindings_chain(self, bindings_chain: bool) -> Self {
        Self { bindings_chain, ..self }
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
        let iter = match self.iter.borrow_mut().take() {
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
        let iter = match self.iter.borrow_mut().take() {
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
