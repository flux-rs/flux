use flux_attrs::*;

/// `ControlFlow` is refined by which arm it is, exactly as [`Result`] is refined by `is_ok`.
///
/// This is what lets the `?` operator carry a discriminant across the desugaring: `?` expands to
/// `Try::branch` followed by `FromResidual::from_residual`, routed through a `ControlFlow`. See
/// the `Try`/`FromResidual` impls for `Option` in `crate::option`.
#[extern_spec(core::ops)]
#[refined_by(is_continue: bool)]
enum ControlFlow<B, C> {
    #[variant((C) -> ControlFlow<B, C>[true])]
    Continue(C),
    #[variant((B) -> ControlFlow<B, C>[false])]
    Break(B),
}
