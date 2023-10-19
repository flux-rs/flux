use std::hash::Hash;
#[flux::opaque]
// #[flux::refined_by(<Tiger> { elems: Set<Tiger> })]
#[flux::refined_by( elems: Set<Tiger> )] //~ ERROR unbound generic `Tiger`
pub struct RSet<Tiger> {
    pub inner: std::collections::HashSet<Tiger>,
}
