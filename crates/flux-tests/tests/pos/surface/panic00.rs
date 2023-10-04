#[flux::sig(fn(b:bool) -> i32[10])]
pub fn test(b: bool) -> i32 {
    if b {
        10
    } else {
        panic!("yikes")
    }
}
