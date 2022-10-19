use std::{cell::RefCell, fmt};

use flux_common::config;
use rustc_hir::def_id::DefId;
use rustc_middle::{mir::Field, ty::TyCtxt};
use rustc_span::{Pos, Span};

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
    ($($ty:ty $(=> $key:literal)?),* $(,)?) => {$(
        impl std::fmt::Debug for $ty  {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                rustc_middle::ty::tls::with(|tcx| {
                    #[allow(unused_mut)]
                    let mut cx = <$ty>::default_cx(tcx);
                    $(
                    if let Some(opts) = flux_common::config::CONFIG_FILE
                        .get("dev")
                        .and_then(|dev| dev.get("pprint"))
                        .and_then(|pprint| pprint.get($key))
                    {
                        cx.merge(opts);
                    }
                    )?
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
    pub preds_chain: bool,
    pub full_spans: bool,
    pub hide_uninit: bool,
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

macro_rules! set_opts {
    ($cx:expr, $opts:expr, [$($opt:ident),+]) => {
        $(
        if let Some(val) = $opts.get(stringify!($opt)).and_then(|v| FromOpt::from_opt(v)) {
            $cx.$opt = val;
        }
        )+
    };
}

impl PPrintCx<'_> {
    pub fn default(tcx: TyCtxt) -> PPrintCx {
        PPrintCx {
            tcx,
            kvar_args: Visibility::Show,
            fully_qualified_paths: false,
            simplify_exprs: true,
            tags: true,
            bindings_chain: true,
            preds_chain: true,
            full_spans: false,
            hide_uninit: true,
        }
    }

    pub fn merge(&mut self, opts: &config::Value) {
        set_opts!(
            self,
            opts,
            [
                kvar_args,
                fully_qualified_paths,
                simplify_exprs,
                tags,
                bindings_chain,
                preds_chain,
                full_spans,
                hide_uninit
            ]
        );
    }

    pub fn kvar_args(self, kvar_args: Visibility) -> Self {
        Self { kvar_args, ..self }
    }

    pub fn fully_qualified_paths(self, b: bool) -> Self {
        Self { fully_qualified_paths: b, ..self }
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
        define_scoped!(cx, f);

        let path = cx.tcx.def_path(*self);
        if cx.fully_qualified_paths {
            let krate = cx.tcx.crate_name(self.krate);
            w!("{}{}", ^krate, ^path.to_string_no_crate_verbose())
        } else {
            w!("{}", ^path.data.last().unwrap())
        }
    }
}

pub fn def_id_to_string(def_id: DefId) -> String {
    rustc_middle::ty::tls::with(|tcx| format!("{:?}", WithCx::new(&PPrintCx::default(tcx), def_id)))
}

impl Pretty for Field {
    fn fmt(&self, _cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_u32())
    }
}

impl Pretty for Span {
    fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if cx.full_spans {
            write!(f, "{self:?}")
        } else {
            let src_map = cx.tcx.sess.source_map();
            let lo = src_map.lookup_char_pos(self.lo());
            let hi = src_map.lookup_char_pos(self.hi());
            // use rustc_span::FileName;
            // match lo.file.name {
            //     FileName::Real(ref name) => {
            //         write!(
            //             f,
            //             "{}",
            //             name.local_path_if_available()
            //                 .file_name()
            //                 .unwrap()
            //                 .to_string_lossy()
            //         )
            //     }
            //     FileName::QuoteExpansion(_) => write!(f, "<quote expansion>"),
            //     FileName::MacroExpansion(_) => write!(f, "<macro expansion>"),
            //     FileName::Anon(_) => write!(f, "<anon>"),
            //     FileName::ProcMacroSourceCode(_) => write!(f, "<proc-macro source code>"),
            //     FileName::CfgSpec(_) => write!(f, "<cfgspec>"),
            //     FileName::CliCrateAttr(_) => write!(f, "<crate attribute>"),
            //     FileName::Custom(ref s) => write!(f, "<{}>", s),
            //     FileName::DocTest(ref path, _) => write!(f, "{}", path.display()),
            //     FileName::InlineAsm(_) => write!(f, "<inline asm>"),
            // }?;
            write!(
                f,
                "{}:{}: {}:{}",
                lo.line,
                lo.col.to_usize() + 1,
                hi.line,
                hi.col.to_usize() + 1,
            )
        }
    }
}

trait FromOpt: Sized {
    fn from_opt(opt: &config::Value) -> Option<Self>;
}

impl FromOpt for bool {
    fn from_opt(opt: &config::Value) -> Option<Self> {
        opt.as_bool()
    }
}

impl FromOpt for Visibility {
    fn from_opt(opt: &config::Value) -> Option<Self> {
        match opt.as_str() {
            Some("show") => Some(Visibility::Show),
            Some("hide") => Some(Visibility::Hide),
            Some(s) => {
                let n = s
                    .strip_prefix("truncate(")?
                    .strip_suffix(')')?
                    .parse()
                    .ok()?;
                Some(Visibility::Truncate(n))
            }
            _ => None,
        }
    }
}
