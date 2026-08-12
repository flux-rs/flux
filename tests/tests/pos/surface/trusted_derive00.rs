// Test that `#[flux::trusted_derive]` opts a type's derive-generated code out of checking.

// The derived `Debug`/`Hash` read the internal representation of an opaque struct, which flux
// cannot check. Derive-generated code can't be annotated directly, so the *type* opts out.
#[derive(Debug, Clone, Copy, Hash)]
#[flux::opaque]
#[flux::trusted_derive]
#[flux::refined_by(n: int)]
pub struct Opaque(u32);

// Same, with a reason.
#[derive(Debug, Hash)]
#[flux::opaque]
#[flux::trusted_derive(reason = "the derived code reads the opaque representation")]
#[flux::refined_by(n: int)]
pub struct OpaqueWithReason(u32);

// The explicit `yes` form is also accepted.
#[derive(Debug, Hash)]
#[flux::opaque]
#[flux::trusted_derive(yes)]
#[flux::refined_by(n: int)]
pub struct OpaqueExplicitYes(u32);

// The attribute is accepted on enums too (`derive_self_ty` resolves any local ADT).
#[derive(Debug, Hash)]
#[flux::trusted_derive]
pub enum MyEnum {
    A(u32),
    B,
}

// A type with no derives at all is unaffected by the attribute.
#[flux::opaque]
#[flux::trusted_derive]
#[flux::refined_by(n: int)]
pub struct NoDerives(u32);
