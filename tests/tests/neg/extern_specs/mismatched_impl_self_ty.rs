// Test that extern spec for trait impl rejects mismatched self types.
// Generic params match the external impl, but the self type is more specific.
// Issue: https://github.com/flux-rs/flux/issues/833

#![feature(step_trait)]
use std::iter::Step;

use flux_attrs::extern_spec;

#[extern_spec(std::ops)]
impl<A: Step> Iterator for Range<usize> {} //~ ERROR invalid extern spec for trait impl
