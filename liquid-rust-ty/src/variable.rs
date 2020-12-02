use crate::argument::Argument;

use std::fmt;

#[derive(Clone, Copy, Debug)]
pub enum Variable<V> {
    Bounded,
    Arg(Argument),
    Free(V),
}

impl<V> From<V> for Variable<V> {
    fn from(free: V) -> Self {
        Self::Free(free)
    }
}

impl<V: fmt::Display> fmt::Display for Variable<V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bounded => "b".fmt(f),
            Self::Arg(arg) => arg.fmt(f),
            Self::Free(free) => free.fmt(f),
        }
    }
}
