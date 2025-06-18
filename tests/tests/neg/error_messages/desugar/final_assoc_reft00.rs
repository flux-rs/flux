#[flux::assoc(final fn foo() -> bool)] //~ERROR final associated refinements must have a body
pub trait MyTrait {}
