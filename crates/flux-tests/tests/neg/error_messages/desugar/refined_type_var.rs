#![feature(register_tool)]
#![register_tool(flux)]

struct S<T> {
    #[flux::field(T{v: v > 0})] //~ ERROR type cannot be refined
    x: T,
}

enum E<T> {
    #[flux::variant((T[@n, @m]) -> E<T>)] //~ ERROR type cannot be refined
    A(T),
}
