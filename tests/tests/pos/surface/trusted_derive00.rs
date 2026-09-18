// Test that derive-generated code is skipped for types that trust their derives, either
// implicitly via `#[flux::opaque]` or explicitly via `#[flux::trusted_derive]`.

// A `#[flux::opaque]` type implicitly trusts its derives: the derived `Debug`/`Hash` read the
// internal representation, which is exactly what opacity forbids, so no annotation is needed.
#[derive(Debug, Clone, Copy, Hash)]
#[flux::opaque]
#[flux::refined_by(n: int)]
pub struct ImplicitlyTrusted(u32);

// The explicit annotation is still accepted (and is what a non-opaque type would use).
#[derive(Debug, Hash)]
#[flux::opaque]
#[flux::trusted_derive]
#[flux::refined_by(n: int)]
pub struct Explicit(u32);

// ... with a reason,
#[derive(Debug, Hash)]
#[flux::opaque]
#[flux::trusted_derive(reason = "the derived code reads the opaque representation")]
#[flux::refined_by(n: int)]
pub struct ExplicitWithReason(u32);

// ... and with the explicit `yes`.
#[derive(Debug, Hash)]
#[flux::opaque]
#[flux::trusted_derive(yes)]
#[flux::refined_by(n: int)]
pub struct ExplicitYes(u32);

// The attribute is accepted on enums too (`derive_self_ty` resolves any local ADT).
#[derive(Debug, Hash)]
#[flux::trusted_derive]
pub enum MyEnum {
    A(u32),
    B,
}

// A type with no derives at all is unaffected.
#[flux::opaque]
#[flux::refined_by(n: int)]
pub struct NoDerives(u32);
