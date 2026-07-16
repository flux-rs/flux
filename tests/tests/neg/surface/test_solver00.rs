#[flux::opts(solver = "z3")]
#[flux::spec(fn(x:i32) -> i32{v: v > x})]
pub fn inc(x: i32) -> i32 {
    x + 1
}

#[flux::opts(solver = "cvc5")]
#[flux::spec(fn(x:i32) -> i32{v: v < x})]
pub fn dec(x: i32) -> i32 {
    x - 1
}

#[flux::opts(solver = "spacer")]
#[flux::spec(fn(x:i32) -> i32{v: v < x})]
pub fn dec_spacer(x: i32) -> i32 {
    x + 99 //~ ERROR refinement type
}
