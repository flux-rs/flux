use std::{
    cell::RefCell,
    fmt::{self, Write},
};

use itertools::{Format, Itertools};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

use crate::{
    intern::{Internable, Interned},
    ty::{BaseTy, BinOp, ExprKind, ExprS, ParamTy, Pred, RegionS, Ty, TyKind, TyS, Var},
    tyenv::{RegionKind, TyEnv},
};

macro_rules! define_scoped {
    ($cx:ident, $fmt:ident) => {
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

macro_rules! w {
    ($fmt:literal, $($args:tt)*) => {
        w!(@go ($fmt; $($args)*) -> ())
    };
    ($fmt:literal) => {
        write!(scoped_fmt!(), $fmt)
    };
    (@go ($fmt:literal; ^$head:expr, $($tail:tt)*) -> ($($accum:tt)*)) => {
        w!(@go ($fmt; $($tail)*) -> ($($accum)* $head,))
    };
    (@go ($fmt:literal; $head:expr, $($tail:tt)*) -> ($($accum:tt)*)) => {
        w!(@go ($fmt; $($tail)*) -> ($($accum)* WithCx::new(scoped_cx!(), $head),))
    };
    (@go ($fmt:literal; ^$head:expr) -> ($($accum:tt)*)) => {
        w!(@as_expr write!(scoped_fmt!(), $fmt, $($accum)* $head,))
    };
    (@go ($fmt:literal; $head:expr) -> ($($accum:tt)*)) => {
        w!(@as_expr write!(scoped_fmt!(), $fmt, $($accum)* WithCx::new(scoped_cx!(), $head),))
    };
    (@as_expr $e:expr) => { $e };
}

macro_rules! join {
    ($sep:expr, $iter:expr) => {
        Join {
            sep: $sep,
            iter: RefCell::new(Some($iter.into_iter())),
        }
    };
}

macro_rules! impl_debug_with_default_cx {
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

pub struct PPrintCx<'tcx> {
    tcx: TyCtxt<'tcx>,
    print_vars_in_scope: bool,
    fully_qualified_paths: bool,
}

struct WithCx<'a, 'tcx, T> {
    data: T,
    cx: &'a PPrintCx<'tcx>,
}

struct Join<'a, I> {
    sep: &'a str,
    iter: RefCell<Option<I>>,
}

trait Pretty {
    fn fmt(&self, cx: &PPrintCx, f: &mut fmt::Formatter<'_>) -> fmt::Result;

    fn default_cx(tcx: TyCtxt) -> PPrintCx {
        PPrintCx::default(tcx)
    }
}

impl PPrintCx<'_> {
    fn default(tcx: TyCtxt) -> PPrintCx {
        PPrintCx {
            tcx,
            print_vars_in_scope: true,
            fully_qualified_paths: false,
        }
    }

    fn print_vars_in_scope(self, b: bool) -> Self {
        Self {
            print_vars_in_scope: b,
            ..self
        }
    }

    fn fully_qualified_paths(self, b: bool) -> Self {
        Self {
            fully_qualified_paths: b,
            ..self
        }
    }
}

impl<'a, 'tcx, T> WithCx<'a, 'tcx, T> {
    fn new(cx: &'a PPrintCx<'tcx>, data: T) -> Self {
        Self { data, cx }
    }
}

impl<T: Pretty> Pretty for &'_ T {
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
        PPrintCx::default(tcx).print_vars_in_scope(false)
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
            Self::KVar(kvid, args) => {
                if cx.print_vars_in_scope {
                    w!("{:?}({:?})", ^kvid, join!(", ", args))
                } else {
                    w!("{:?}", ^kvid)
                }
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
                w!(" {} ", ^op)?;
                if should_parenthesize(*op, e2) {
                    w!("({:?})", e2)?;
                } else {
                    w!("{:?}", e2)?;
                }
                Ok(())
            }
            ExprKind::Constant(c) => w!("{}", ^c),
            ExprKind::UnaryOp(op, e) => {
                if matches!(e.kind(), ExprKind::Var(_) | ExprKind::Constant(_)) {
                    w!("{}{:?}", ^op, e)
                } else {
                    w!("{}({:?})", ^op, e)
                }
            }
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
