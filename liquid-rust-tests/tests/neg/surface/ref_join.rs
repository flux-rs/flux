#![feature(register_tool)]
#![register_tool(lr)]

#[lr::sig(fn(b:bool{b == true}) -> i32{v:v == 0})]
pub fn assert(_b: bool) -> i32 {
    0
}

#[lr::sig(fn(b:bool) -> i32{v:v==0})]
pub fn ref_join(b: bool) -> i32 {
    let x = 1;
    let y = 2;
    let r;
    if b {
        r = &x;
    } else {
        r = &y;
    }
    assert(*r - 1 > 0); //~ ERROR precondition might not hold
    0
}
