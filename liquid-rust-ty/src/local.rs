use liquid_rust_common::def_index;

use std::fmt;

def_index!(LocalVariable);

impl fmt::Display for LocalVariable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "x{}", self.0)
    }
}
