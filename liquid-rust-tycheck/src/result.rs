use liquid_rust_mir::Span;
use liquid_rust_ty::{BaseTy, Ty};

pub type TyResult<T = ()> = Result<T, TyError>;

#[derive(Debug)]
pub struct TyError {
    pub kind: TyErrorKind,
    pub span: Span,
}

impl TyError {
    pub(crate) fn with_span(self, span: Span) -> TyError {
        TyError {
            kind: self.kind,
            span,
        }
    }
}

#[derive(Debug)]
pub enum TyErrorKind {
    ShapeMismatch { expected: Ty, found: Ty },
    BaseMismatch { expected: BaseTy, found: Ty },
}
