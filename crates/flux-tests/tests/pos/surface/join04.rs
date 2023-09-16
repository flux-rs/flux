#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(bool) -> i32{v: v > 0})]
fn join_arr(b: bool) -> i32 {
    let arr = if b { [1, 2] } else { [3, 4] };
    arr[0]
}
