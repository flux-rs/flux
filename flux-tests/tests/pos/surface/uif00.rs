#![feature(register_tool)]
#![register_tool(flux)]
#![feature(custom_inner_attributes)]
#![flux::defs {
    fn valid(x:int) -> bool;
}]

#[flux::trusted]
#[flux::sig(fn(x:i32) -> bool[valid(x)])]
fn valid(x: i32) -> bool {
    0 <= x && x <= 100
}

#[flux::sig(fn (i32{v:valid(v)}) -> i32)]
fn bar(a: i32) -> i32 {
    return a;
}

#[flux::sig(fn(i32))]
pub fn test(n: i32) {
    let ok = valid(n);
    if ok {
        bar(n);
    }
}
