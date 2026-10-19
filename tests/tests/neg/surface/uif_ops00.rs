// With `uif_ops = "*"`, `x * y` is encoded as an uninterpreted function, so e.g. commutativity no
// longer holds
#[flux::opts(uif_ops = "*")]
#[flux::sig(fn(x: i32, y: i32) -> i32[y * x])]
pub fn mul_comm_uif(x: i32, y: i32) -> i32 {
    x * y //~ ERROR refinement type
}

#[flux::opts(uif_ops = "*, /, +")]
#[flux::sig(fn(x: i32, y: i32) -> i32[y + x])]
pub fn add_comm_uif(x: i32, y: i32) -> i32 {
    x + y //~ ERROR refinement type
}

#[flux::opts(uif_ops = "+")]
#[flux::sig(fn(x: i32) -> i32[x + 1])]
pub fn add_one(x: i32) -> i32 {
    1 + x //~ ERROR refinement type
}
