#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(i32) -> i32[0])]
pub fn generalized_join(n: i32) -> i32 {
    let mut i = 0;
    let mut j = 0;
    while i < n {
        i += 1;
        j += 1;
    }
    i - j
}
