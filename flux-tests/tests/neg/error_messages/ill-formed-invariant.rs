#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(n: int)]
#[flux::invariant(n + 1)] //~ ERROR mismatched sorts
pub enum A {
    #[flux::variant(E[0])]
    V,
}

#[flux::refined_by(n: int)]
#[flux::invariant(nn > 0)] //~ ERROR cannot find
pub enum B {
    #[flux::variant(E[0])]
    V,
}
