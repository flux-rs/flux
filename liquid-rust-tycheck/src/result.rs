use liquid_rust_ty::Ty;

pub type TyResult<S, T = ()> = Result<T, TyError<S>>;

#[derive(Debug)]
pub struct TyError<S> {
    pub kind: TyErrorKind,
    pub span: S,
}

#[derive(Debug)]
pub enum TyErrorKind {
    ShapeMismatch { expected: Ty, found: Ty },
}
