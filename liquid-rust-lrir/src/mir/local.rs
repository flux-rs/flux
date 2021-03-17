use crate::mir::Span;

use liquid_rust_common::new_index;
use rustc_middle::ty as lr;

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

pub struct LocalDecl<'tcx> {
    pub is_mutable: bool,
    pub ty: lr::Ty<'tcx>,
    pub span: Span,
}
