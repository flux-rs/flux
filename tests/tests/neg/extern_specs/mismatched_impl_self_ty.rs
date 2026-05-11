// Test that extern spec for trait impl rejects mismatched self types
// Issue: https://github.com/flux-rs/flux/issues/833

#[flux::extern_spec(std::ops)]
impl Iterator for std::ops::Range<usize> {} //~ ERROR invalid extern spec for trait impl
