use liquid_rust_common::{index::Index, new_index};
use liquid_rust_ty::LocalVariable;

use std::fmt;

new_index! {
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    Local
}

impl Local {
    pub const fn ret() -> Self {
        Self(0)
    }
}

impl From<Local> for LocalVariable {
    fn from(local: Local) -> Self {
        LocalVariable::new(local.index())
    }
}

impl fmt::Display for Local {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "_{}", self.0)
    }
}
