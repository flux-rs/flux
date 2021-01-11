use liquid_rust_ty::{BaseTy, Ty};

pub type TyResult<S, T = ()> = Result<T, TyError<S>>;

#[derive(Debug)]
pub struct TyError<S> {
    pub kind: TyErrorKind,
    pub span: S,
}

impl TyError<()> {
    pub(crate) fn with_span<S>(self, span: S) -> TyError<S> {
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
