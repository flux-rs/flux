#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn() -> Vec<i32{v: v >= 0}>)]
pub fn move_out_of_box() -> Vec<i32> {
    let mut vec = Vec::new();
    vec.push(0);
    vec.push(0);
    // move out of box
    *Box::new(vec)
}

#[flux::sig(fn() -> Box<i32[2]>)]
pub fn close_at_return() -> Box<i32> {
    let mut x = Box::new(1);
    // update through box to open it
    *x += 1;
    // we should close it before returning
    x
}

#[flux::sig(fn(bool) -> Box<i32{v : v > 0}>)]
pub fn close_at_join(b: bool) -> Box<i32> {
    let mut x = Box::new(1);
    if b {
        // we only open the box in one branch
        *x += 1;
    }
    // box should be closed here
    x
}

#[flux::sig(fn(bool) -> i32{v : v > 2})]
pub fn no_close_join(b: bool) -> i32 {
    let mut x = Box::new(1);
    *x += 1;
    if b {
        *x += 1;
    } else {
        *x += 2;
    }
    // check if we handle the case where the box was open before
    // branching and stays open.
    *x
}

struct S {
    #[flux::field(i32{v : v > 0})]
    x: i32,
}

pub fn close_on_move() {
    let mut b = Box::new(S { x: 1 });
    // open the box and mutate the inner struct maintaining the invariant
    (*b).x += 1;
    // check we properly close the box when moving out of it
    std::mem::drop(b);
}
