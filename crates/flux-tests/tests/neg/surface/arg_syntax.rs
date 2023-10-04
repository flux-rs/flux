#[flux::sig(fn(x: i32{v: v > 0 && v < 10}) -> i32{v: v < 10})]
fn exists(x: i32) -> i32 {
    x + 1 //~ ERROR refinement type
}

#[flux::sig(fn(x: &i32[@n]) -> i32[n + 1])]
fn shr_ref(x: &i32) -> i32 {
    *x + 2 //~ ERROR refinement type
}

#[flux::sig(fn(x: i32) -> i32[x + 1])]
fn path(x: i32) -> i32 {
    x + 2 //~ ERROR refinement type
}

#[flux::sig(fn(x: [i32{v : v >= 0}; 1]) -> [i32{v : v > 0}; 1])]
fn arr(x: [i32; 1]) -> [i32; 1] {
    x //~ ERROR refinement type
}

#[flux::sig(fn(x: &[i32{v : v >= 0}]) -> &[i32{v : v > 0}])]
fn slice(x: &[i32]) -> &[i32] {
    x //~ ERROR refinement type
}
