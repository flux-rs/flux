use std::fmt;

pub type Ctx = usize;

pub trait Emit {
    fn emit<W: fmt::Write>(&self, w: &mut W, ctx: &Ctx) -> fmt::Result;
}

impl<E: Emit> Emit for Box<E> {
    fn emit<W: fmt::Write>(&self, w: &mut W, ctx: &Ctx) -> fmt::Result {
        self.as_ref().emit(w, ctx)
    }
}

impl<E: Emit> Emit for &E {
    fn emit<W: fmt::Write>(&self, w: &mut W, ctx: &Ctx) -> fmt::Result {
        (*self).emit(w, ctx)
    }
}

pub(crate) struct Emitter<'fix, E: Emit> {
    inner: E,
    ctx: &'fix Ctx,
}

impl<'fix, E: Emit> Emitter<'fix, E> {
    pub(crate) fn new(inner: E, ctx: &'fix Ctx) -> Self {
        Self { inner, ctx }
    }
}

impl<'fix, E: Emit> fmt::Display for Emitter<'fix, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.emit(f, self.ctx)
    }
}

#[macro_export]
macro_rules! emit {
    ($dst:expr, $ctx:expr, $fmt:expr) => {
        write!($dst, $fmt)
    };
    ($dst:expr, $ctx:expr, $fmt:expr, $($args:tt),*) => {
        write!($dst, $fmt, $($crate::emit::Emitter::new($args, $ctx),)*)
    }
}

#[macro_export]
macro_rules! impl_emit_by_display {
    ($type:ident) => {
        impl $crate::Emit for $type {
            fn emit<W: fmt::Write>(&self, w: &mut W, _: &$crate::emit::Ctx) -> fmt::Result {
                write!(w, "{}", self)
            }
        }
    };
}

impl_emit_by_display!(usize);
