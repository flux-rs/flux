use std::fmt;

#[derive(Clone, Copy, Debug)]
pub enum Variable<A> {
    Free(A),
    Bounded,
}

impl<A> Variable<A> {
    pub fn map<B>(self, f: impl Fn(A) -> B) -> Variable<B> {
        match self {
            Self::Bounded => Variable::Bounded,
            Self::Free(a) => Variable::Free(f(a)),
        }
    }
}

impl<A> From<A> for Variable<A> {
    fn from(free_variable: A) -> Self {
        Self::Free(free_variable)
    }
}

impl<A: fmt::Display> fmt::Display for Variable<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Free(a) => a.fmt(f),
            Self::Bounded => "b".fmt(f),
        }
    }
}
