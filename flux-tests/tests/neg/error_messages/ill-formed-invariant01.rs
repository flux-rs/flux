#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(n: int)]
#[flux::invariant(n + 1)] //~ ERROR mismatched sorts
pub enum E {
    #[flux::variant(E[0])]
    V,
}
