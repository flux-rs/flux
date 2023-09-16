#![feature(register_tool)]
#![register_tool(flux)]

#[flux::opaque]
struct Ptr<T> {
    data: *mut T,
}
