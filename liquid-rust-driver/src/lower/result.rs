use liquid_rust_lrir::mir::Span;

pub type LowerResult<T> = Result<T, LowerError>;

pub struct LowerError {
    pub kind: LowerErrorKind,
    pub span: Span,
}

pub enum LowerErrorKind {}
