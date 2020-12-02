use liquid_rust_common::def_index;

use std::fmt;

def_index!(Local);

impl fmt::Display for Local {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "_{}", self.0)
    }
}
