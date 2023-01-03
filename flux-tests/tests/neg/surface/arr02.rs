#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn() -> i32{v: v == 1})]
fn test00() -> i32 {
    let v1 = 0;
    let v2 = 0;
    let arr = [&v1, &v2];
    *arr[0] //~ ERROR postcondition
}

#[flux::sig(fn() -> i32{v: v > 0})]
fn test01() -> i32 {
    let mut v1 = 0;
    let mut v2 = 0;
    let arr = [&mut v1, &mut v2];
    *arr[1] += 1;
    v1 //~ ERROR postcondition
}
