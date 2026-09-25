#[flux::sig(fn(x: i32, y: i32) -> bool[(x < y) == true])]
pub fn grouped_left(x: i32, y: i32) -> bool {
    x < y
}

#[flux::sig(fn(x: i32, y: i32) -> bool[true == (x < y)])]
pub fn grouped_right(x: i32, y: i32) -> bool {
    x < y
}

#[flux::sig(fn(x: i32, y: i32, z: i32) -> bool[(x < y) == (y < z)])]
pub fn grouped_both(x: i32, y: i32, z: i32) -> bool {
    (x < y) == (y < z)
}
