#![feature(register_tool)]
#![register_tool(flux)]

// Read through box under & ref
#[flux::sig(fn(&Box<i32{v : v >= 0}>) -> i32{v : v > 0})]
pub fn shared_ref_box(x: &Box<i32>) -> i32 {
    **x + 1
}

// Mutate through box under &mut ref
#[flux::sig(fn(&mut Box<i32{v : v >= 0}>))]
pub fn mut_ref_box(x: &mut Box<i32>) {
    **x += 1;
}
