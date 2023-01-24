#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(a: int)]
struct S {
    #[flux::field(i31[@a])] //~ ERROR cannot resolve
    f: i32,
}
