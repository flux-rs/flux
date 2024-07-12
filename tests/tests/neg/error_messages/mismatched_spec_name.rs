#[flux::spec(
fn fooo(x: i32) -> i32{v: v > 0} //~ ERROR name in function spec doesn't match item's name
)]
fn foo(x: i32) -> i32 {
    1
}
