use liquid_rust_common::new_index;

use std::fmt;

new_index! {
    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    LocalVariable
}

impl fmt::Display for LocalVariable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "x{}", self.0)
    }
}
