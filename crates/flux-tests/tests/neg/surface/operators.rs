#[flux::sig(fn(x: i32, y: i32{y == -x}))]
pub fn test_neg00(x: i32, y: i32) {}

pub fn test_neg01() {
    test_neg00(1, 1); //~ ERROR refinement type
}

#[flux::sig(fn(x: i32) -> i32[x/2])]
pub fn test_div(x: i32) -> i32 {
    x / 2 + 1 //~ ERROR refinement type
}

#[flux::sig(fn(x:i32, y: i32{x != y}))]
pub fn test_neq00(x: i32, y: i32) {}

pub fn test_neq01() {
    test_neq00(0, 0); //~ ERROR refinement type
}

#[flux::sig(fn(x:i32{!(x > 0)}))]
pub fn test_not00(x: i32) {}

pub fn test_not01() {
    test_not00(1); //~ ERROR refinement type
}

#[flux::sig(fn(bool[@x], bool[!x]))]
pub fn test_not02(x: bool, y: bool) {}

pub fn test_not03() {
    test_not02(true, true); //~ ERROR refinement type
}
