use crate::Fixpoint;

use std::fmt;

pub(crate) trait Emit {
    fn emit<W: fmt::Write>(&self, w: &mut W, fixpoint: &Fixpoint) -> fmt::Result;
}

impl<E: Emit> Emit for Box<E> {
    fn emit<W: fmt::Write>(&self, w: &mut W, fixpoint: &Fixpoint) -> fmt::Result {
        self.as_ref().emit(w, fixpoint)
    }
}

impl<E: Emit> Emit for &E {
    fn emit<W: fmt::Write>(&self, w: &mut W, fixpoint: &Fixpoint) -> fmt::Result {
        (*self).emit(w, fixpoint)
    }
}

pub(crate) struct Emitter<'fix, E: Emit> {
    inner: E,
    fixpoint: &'fix Fixpoint,
}

impl<'fix, E: Emit> Emitter<'fix, E> {
    pub(crate) fn new(inner: E, fixpoint: &'fix Fixpoint) -> Self {
        Self { inner, fixpoint }
    }
}

impl<'fix, E: Emit> fmt::Display for Emitter<'fix, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.inner.emit(f, self.fixpoint)
    }
}

#[macro_export]
macro_rules! emit {
    ($dst:expr, $fix:expr, $fmt:expr) => {
        write!($dst, $fmt)
    };
    ($dst:expr, $fix:expr, $fmt:expr, $($args:tt),*) => {
        write!($dst, $fmt, $($crate::emit::Emitter::new($args, $fix),)*)
    }
}

#[macro_export]
macro_rules! impl_emit_by_display {
    ($type:ident) => {
        impl $crate::Emit for $type {
            fn emit<W: fmt::Write>(&self, w: &mut W, _: &$crate::Fixpoint) -> fmt::Result {
                write!(w, "{}", self)
            }
        }
    };
}
