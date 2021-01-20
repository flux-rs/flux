use crate::{argument::Argument, local::LocalVariable};

use std::fmt;

/// A variable of a predicate.
#[derive(Clone, Copy, Debug)]
pub enum Variable {
    /// A variable bound by a refined base type, e.g the `b` in `{ b: usize | b > 0 }`.
    Bound,
    /// A variable bound by a dependent function type, e.g the `x` in `fn(x: usize) -> usize`.
    Arg(Argument),
    /// A variable bound to a local in the current environment. This is used by the `tycheck`
    /// module to refer to the locals inside a function.
    Local(LocalVariable),
}

impl From<LocalVariable> for Variable {
    fn from(local: LocalVariable) -> Self {
        Self::Local(local)
    }
}

impl From<Argument> for Variable {
    fn from(argument: Argument) -> Self {
        Self::Arg(argument)
    }
}

impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bound => "b".fmt(f),
            Self::Arg(arg) => arg.fmt(f),
            Self::Local(local) => local.fmt(f),
        }
    }
}
