#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(bool[true]))]
pub fn assert(_b: bool) {}

#[flux::sig(fn (y:i32{v:0<=v}) -> impl Future<Output=i32{v:v <= 1000 }>)]
pub async fn bar(y: i32) -> i32 {
    let z = if y > 10 { 1 } else { 0 };
    assert(z >= 0);
    assert(y >= 0);
    z + 999
}

#[flux::sig(fn (y:i32{v:0<=v}) -> impl Future<Output=i32{v:v < 1000 }>)]
pub async fn foo(y: i32) -> i32 {
    let z = if y > 10 { 1 } else { 0 };
    assert(z >= 0);
    assert(y >= 0);
    z + 999 //~ ERROR refinement type
}
