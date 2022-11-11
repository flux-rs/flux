#![feature(register_tool, box_patterns)]
#![register_tool(flux)]

struct S {
    #[flux::field(i64)] //~ ERROR invalid refinement annotation
    x: i32,
    y: i64,
}
