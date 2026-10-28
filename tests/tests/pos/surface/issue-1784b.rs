// Join points right after an empty `if`, including loops that carry state (see #1784).

#[flux::sig(fn(bool[true]))]
fn assert(_b: bool) {}

pub fn test1(b: bool) -> i32 {
    let mut i = 0;
    if b {}
    while i < 10 {
        i += 1;
    }
    assert(i >= 0);
    i
}

// What is known before the `if` must still be usable in the loop
#[flux::sig(fn(b: bool, n: i32{n > 0}) -> i32{v: v > 0})]
pub fn test2(b: bool, n: i32) -> i32 {
    let mut i = n;
    if b {}
    while i < 10 {
        i += 1;
    }
    i
}

pub fn test3(a: bool, b: bool) {
    if a {
        if b {}
    }
    loop {}
}
