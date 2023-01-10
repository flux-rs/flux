#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(n: int)]
#[flux::invariant(nn > 0)] //~ ERROR cannot find
pub enum E {
    #[flux::variant(E[0])]
    V,
}
