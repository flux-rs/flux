#![feature(register_tool)]
#![register_tool(flux)]

pub trait Easy {
    type Thing;
}

impl<T> Easy for Option<T> {
    type Thing = T;
}

//#[flux::sig(fn foo() -> impl Easy<Thing=i32{v:0<=v}>)]
pub fn foo() -> impl Easy<Thing = i32> {
    Some(10) // Option<i32[10]>
}
/*

// fn(x:i32) -> impl Future<Output=i32{v: 0 < v}>
async fn(x:i32) -> i32{v: 0 < v} {
    10
}

// fn(x:i32) -> impl Future<Output=i32{v: x < v}>
async fn(x:i32) -> i32{v: x < v} {
    x + 1
}
*/
