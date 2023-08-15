#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(bool[true]))]
pub fn assert(_b: bool) {}

#[flux::sig(async fn (y:i32{v:0<=v}) -> i32{v:v <= 1000})]
pub async fn bar(y: i32) -> i32 {
    let z = if y > 10 { 1 } else { 0 };
    assert(z >= 0);
    assert(y >= 0);
    z + 999
}

#[flux::sig(async fn (y:i32{v:0<=v}) -> i32{v:v < 1000 })]
pub async fn foo(y: i32) -> i32 {
    let z = if y > 10 { 1 } else { 0 };
    assert(z >= 0);
    assert(y >= 0);
    z + 999 //~ ERROR refinement type
}

#[flux::sig(async fn () -> i32{v:v < 2000 })]
pub async fn baz() -> i32 {
    let a = foo(10).await;
    let b = foo(20).await;
    a + b
}

#[flux::sig(async fn () -> i32{v:v < 1500 })]
pub async fn jazz() -> i32 {
    let a = foo(10).await;
    let b = foo(20).await;
    a + b //~ ERROR refinement type
}
