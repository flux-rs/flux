use liquid_rust_common::def_index;
use liquid_rust_ty::Argument;

use std::fmt;

def_index!(Local);

impl Local {
    pub fn try_from_argument(argument: Argument) -> Result<Self, usize> {
        match argument.level() {
            0 => Ok(Local(argument.pos() + 1)),
            level => Err(level),
        }
    }
}

impl fmt::Display for Local {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "_{}", self.0)
    }
}
