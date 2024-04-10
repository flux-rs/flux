#[flux::sig(fn(bool) -> i32{v: v >= 0})]
pub fn test00(b: bool) -> i32 {
    let p = if b { (0, 0) } else { (0, 1) };
    p.0 + p.1
}
