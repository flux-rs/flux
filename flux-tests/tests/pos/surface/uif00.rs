#![feature(register_tool)]
#![register_tool(flux)]
#![feature(custom_inner_attributes)]
#![flux::uf(fn valid(int) -> bool)]

#[flux::assume]
#[flux::sig(fn(x:i32) -> bool[valid(x)])]
fn valid(x: i32) -> bool {
    0 <= x && x <= 100
}

#[flux::sig(fn (i32{v:valid(v)}) -> ())]
fn bar(a: i32) {
    return;
}

#[flux::sig(fn(i32) -> ())]
pub fn test(n: i32) {
    let ok = valid(n);
    if ok {
        bar(n);
    }
}
