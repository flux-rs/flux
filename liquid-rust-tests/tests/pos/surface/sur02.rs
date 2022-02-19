#![feature(register_tool)]
#![register_tool(lr)]

// TODO: this should say `&mut n` instead of `& n` but I can't get it to parse :-(

#[lr::sig(fn(x: & n@i32) -> i32; x: i32{v: v == n + 1})]
pub fn inc(x: &mut i32) -> i32 {
    *x += 1;
    0
}
