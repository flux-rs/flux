// Without `uif_ops`, `*` is interpreted, so e.g. commutativity holds
#[flux::sig(fn(x: i32, y: i32) -> i32[y * x])]
pub fn mul_comm(x: i32, y: i32) -> i32 {
    x * y
}

// With `uif_ops = "*"`, `x * y` is encoded as an uninterpreted function, so the same term is still
// provable (by congruence)
#[flux::opts(uif_ops = "*")]
#[flux::sig(fn(x: i32, y: i32) -> i32[x * y])]
pub fn mul_uif(x: i32, y: i32) -> i32 {
    x * y
}

// With `uif_ops = "*"`, `x * y` is encoded as an uninterpreted function, so the same term is still
// provable (by congruence)
#[flux::opts(uif_ops = "*")]
#[flux::sig(fn(x: i32, y: i32) -> i32[x * x])]
pub fn mul_uif_square(x: i32, y: i32) -> i32 {
    if x == y { x * y } else { x * x }
}

// Operations not in `uif_ops` remain interpreted
#[flux::opts(uif_ops = "*,/")]
#[flux::sig(fn(x: i32, y: i32) -> i32[y + x])]
pub fn add_comm(x: i32, y: i32) -> i32 {
    x + y
}

#[flux::opts(uif_ops = "*")]
#[flux::sig(fn(x: i32, y: i32) -> i32[x * y])]
fn mul(x: i32, y: i32) -> i32 {
    x * y
}

// Calls agree on the uninterpreted function
#[flux::opts(uif_ops = "*")]
#[flux::sig(fn(a: i32, b: i32) -> i32[a * b])]
pub fn call_mul(a: i32, b: i32) -> i32 {
    mul(a, b)
}
