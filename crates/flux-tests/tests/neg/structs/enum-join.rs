pub enum Enum<T> {
    A(T),
    B(bool, T),
}

#[flux::sig(fn(Enum<i32{v : v >= 0}>) -> i32{v : v > 0})]
pub fn test(x: Enum<i32>) -> i32 {
    let y = match x {
        Enum::A(n) => n,
        Enum::B(_, n) => n,
    };
    // test we correctly join branches with different variants
    y //~ ERROR refinement type
}

#[flux::sig(fn(Enum<Vec<i32{v: v >= 0}> >) -> Vec<i32{v : v >= 0}>)]
pub fn test2(x: Enum<Vec<i32>>) -> Vec<i32> {
    let mut vec = match x {
        Enum::A(vec) => vec,
        Enum::B(_, vec) => vec,
    };
    // test join of partially moved enum
    vec.push(-1);
    vec
} //~ ERROR refinement type
