use crate::{mir::Span, ty::BaseTy};

use liquid_rust_common::new_index;

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

pub struct LocalDecl {
    pub is_mutable: bool,
    pub ty: BaseTy,
    pub span: Span,
}
