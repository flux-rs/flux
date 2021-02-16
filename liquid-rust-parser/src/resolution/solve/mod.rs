mod ident;
mod predicate;

use crate::{
    ast::{BinOpKind, Span, UnOpKind},
    resolution::ResolutionCtx,
};

use liquid_rust_mir::ty::BaseTy;

pub type ResolutionResult<'source, T> = Result<T, ResolutionError<'source>>;

/// A resolution error.
#[derive(Debug)]
pub struct ResolutionError<'source, S = Span> {
    /// Reason of the error.
    pub kind: ResolutionErrorKind<'source>,
    pub span: S,
}

#[derive(Debug)]
pub enum ResolutionErrorKind<'source> {
    /// Resolution failed because there is an unbound identifier.
    UnboundIdent(&'source str),
    /// Resolution failed because there is an invalid unary operation.
    InvalidUnaryOp(UnOpKind, BaseTy),
    /// Resolution failed because there is an invalid binary operation.
    InvalidBinaryOp(BinOpKind, BaseTy, BaseTy),
    /// Resolution failed because the predicate of a refined type is not boolean.
    NonBoolPredicate,
    /// Resolution failed because a dependent function type has a function typed argument.
    FuncArgument,
}

impl<'source> ResolutionErrorKind<'source> {
    pub(crate) fn into_err<T>(self, span: Span) -> ResolutionResult<'source, T> {
        Err(ResolutionError { kind: self, span })
    }
}

pub(super) trait Solve<'source> {
    type Output;

    fn solve(
        &self,
        rcx: &mut ResolutionCtx<'source>,
    ) -> ResolutionResult<'source, (Self::Output, BaseTy)>;
}
