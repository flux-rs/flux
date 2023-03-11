#![feature(register_tool)]
#![register_tool(flux)]

enum E1<T> {
    #[flux::variant((i32, T) -> i32)] //~ ERROR this type takes 1 refinement argument but 0 were found
    A(i32, T),
}
