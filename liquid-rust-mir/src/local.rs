use liquid_rust_common::new_index;

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

impl fmt::Display for Local {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "_{}", self.0)
    }
}
