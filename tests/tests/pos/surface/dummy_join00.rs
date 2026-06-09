#[flux::spec(fn (x: i32) -> i32{v: 1 <= v && v <= 4})]
pub fn test(x: i32) -> i32 {
    if x == 0 {
        1
    } else if x == 1 {
        2
    } else if x == 2 {
        3
    } else if x == 3 {
        4
    } else {
        test(x - 1)
    }
}
