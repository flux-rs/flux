#![feature(register_tool, custom_inner_attributes)]
#![register_tool(flux)]

#[flux::refined_by(a: int, b: int)]
pub struct Range {
    #[flux::field(i32[a])]
    left: i32,
    #[flux::field(i32[b])]
    right: i32,
}

#[flux::sig(fn(r: Range, b: bool) -> i32[r.a + 1])]
fn test00(mut r: Range, b: bool) -> i32 {
    if b {
        // this is a function call so the `Range` remains folded
        add_right(&mut r, 1);
    }
    r.left //~ ERROR postcondition
}

#[flux::sig(fn(r: &strg Range[@a, @b], n: i32) ensures r: Range[a, b + n])]
fn add_right(r: &mut Range, n: i32) {
    r.right += n;
}
