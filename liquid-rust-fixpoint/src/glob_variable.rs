use std::fmt;

use liquid_rust_common::new_index;

new_index! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    GlobVariable
}

impl fmt::Display for GlobVariable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "g{}", self.0)
    }
}
