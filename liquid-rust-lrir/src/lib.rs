pub mod ty;

#[macro_use]
extern crate liquid_rust_common;

use std::fmt;

new_index! {
    /// A (program) variable local to a function definition.
    Local
}

impl fmt::Display for Local {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "_{}", self.as_usize())
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Proj {
    /// A field projection into a tuple: the 0 in `p.0`.
    Field(usize),
    /// A dereference: `*p`.
    Deref,
}

/// A path to a value starting from a [Local].
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Place {
    pub base: Local,
    pub projs: Vec<Proj>,
}

impl Place {
    pub fn new(base: Local, projs: Vec<Proj>) -> Self {
        Self { base, projs }
    }

    pub fn as_ref(&self) -> PlaceRef {
        PlaceRef::new(self.base, &self.projs)
    }
}

impl From<Local> for Place {
    fn from(base: Local) -> Self {
        Self::new(base, vec![])
    }
}

impl fmt::Display for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_ref())
    }
}

/// Borrowed version of [Place].
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct PlaceRef<'a> {
    pub base: Local,
    pub projs: &'a [Proj],
}

impl<'a> PlaceRef<'a> {
    pub fn new(base: Local, projs: &'a [Proj]) -> Self {
        Self { base, projs }
    }

    pub fn to_owned(&self) -> Place {
        Place::new(self.base, self.projs.iter().copied().collect())
    }
}

impl<'a> From<Local> for PlaceRef<'a> {
    fn from(base: Local) -> Self {
        Self { base, projs: &[] }
    }
}

impl fmt::Display for PlaceRef<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = format!("{}", self.base);
        let mut need_parens = false;
        for proj in self.projs {
            match proj {
                Proj::Field(n) => {
                    if need_parens {
                        s = format!("({}).{}", s, n);
                        need_parens = false;
                    } else {
                        s = format!("{}.{}", s, n);
                    }
                }
                Proj::Deref => {
                    s = format!("*{}", s);
                    need_parens = true;
                }
            }
        }
        write!(f, "{}", s)
    }
}
