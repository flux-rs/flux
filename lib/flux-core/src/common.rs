#![flux::defs {
    fn min(a: int, b: int) -> int { if a < b { a } else { b } }
    fn max(a: int, b: int) -> int { if a > b { a } else { b } }
}]
//! Small spec functions shared across `flux-core`.
//!
//! Import them with `defs! { use crate::common::min; }` rather than redefining them locally, so
//! that every use site denotes the same function.
