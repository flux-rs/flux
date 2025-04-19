// Define a function whose type uses the Horn generic refinement `p`
#[flux::sig(
    fn[hrn p: int -> bool](x: i32, y: i32) -> i32{v: p(v) && v >= x && v >= y}
    requires p(x) && p(y)
)]
fn max(x: i32, y: i32) -> i32 {
    if x > y { x } else { y }
}

// A client of `max` where the generic is instantiated to `|v| {v % 2 == 0}`
#[flux::sig(fn() -> i32{v: v % 2 == 0})]
pub fn test00() -> i32 {
    max(4, 10)
}

// A client of `max` where the generic is instantiated to `|v| {v == 4 || v == 10}`
#[flux::sig(fn() -> i32[10])]
pub fn test01() -> i32 {
    max(4, 10)
}
