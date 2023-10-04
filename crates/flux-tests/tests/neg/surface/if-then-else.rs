#[flux::sig(fn(a: i32, b: i32) -> i32[if a < b { a } else { b }])]
pub fn min(a: i32, b: i32) -> i32 {
    if a <= b {
        b //~ ERROR refinement type
    } else {
        a //~ ERROR refinement type
    }
}
