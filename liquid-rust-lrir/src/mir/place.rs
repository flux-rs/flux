use crate::mir::Local;

use std::fmt;

/// A path to a value starting from a [Local].
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Place {
    pub local: Local,
    pub projection: Vec<PlaceElem>,
}

impl Place {
    pub fn as_ref(&self) -> PlaceRef {
        PlaceRef {
            local: self.local,
            projection: &self.projection,
        }
    }
}

impl fmt::Display for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        PlaceRef::from(self).fmt(f)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PlaceElem {
    /// A field projection into a tuple: the 0 in `p.0`.
    Field(usize),
    /// A dereference: `*p`.
    Deref,
}

#[derive(Clone, Copy)]
pub struct PlaceRef<'a> {
    pub local: Local,
    pub projection: &'a [PlaceElem],
}

impl<'a> From<&'a Place> for PlaceRef<'a> {
    fn from(place: &'a Place) -> Self {
        PlaceRef {
            local: place.local,
            projection: &place.projection,
        }
    }
}

impl From<Local> for PlaceRef<'_> {
    fn from(local: Local) -> Self {
        PlaceRef {
            local,
            projection: &[],
        }
    }
}

impl<'a> fmt::Display for PlaceRef<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = format!("{}", self.local);
        let mut need_parens = false;
        for elem in self.projection {
            match elem {
                PlaceElem::Field(n) => {
                    if need_parens {
                        s = format!("({}).{}", s, n);
                        need_parens = false;
                    } else {
                        s = format!("{}.{}", s, n);
                    }
                }
                PlaceElem::Deref => {
                    s = format!("*{}", s);
                    need_parens = true;
                }
            }
        }
        write!(f, "{}", s)
    }
}
