use crate::mir::Span;

pub use rustc_middle::mir::Local;
use rustc_middle::ty as lr;

pub struct LocalDecl<'tcx> {
    pub is_mutable: bool,
    pub ty: lr::Ty<'tcx>,
    pub span: Span,
}
