#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn() -> Vec<i32{v: v >  0}>)]
pub fn move_out_of_box() -> Vec<i32> {
    let mut vec = Vec::new();
    vec.push(0);
    vec.push(1);
    // move out box
    *Box::new(vec)
} //~ ERROR postcondition

#[flux::sig(fn() -> Box<i32[1]>)]
pub fn close_at_return() -> Box<i32> {
    let mut x = Box::new(1);
    // update through box to open it
    *x += 1;
    // we should close it before returning
    x //~ ERROR postcondition
}

#[flux::sig(fn(bool) -> Box<i32{v : v > 1}>)]
pub fn close_at_join(b: bool) -> Box<i32> {
    let mut x = Box::new(1);
    if b {
        // we only open the box in one branch
        *x += 1;
    }
    // box should be closed here
    x //~ ERROR postcondition
}

#[flux::sig(fn(bool) -> i32{v : v > 3})]
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
    *x //~ ERROR postcondition
}

struct S {
    #[flux::field(i32{v : v > 0})]
    x: i32,
}

pub fn close_on_move() {
    let mut b = Box::new(S { x: 1 });
    // open the box and mutate the inner struct breaking the invariant
    (*b).x -= 1;
    // closing the box causes the struct to be folded and the invariant to be checked
    std::mem::drop(b); //~ ERROR fold
}
