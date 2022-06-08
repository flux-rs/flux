// Based on http://goto.ucsd.edu:8090/index.html#?demo=permalink%2F1642157817_3971.hs
// This shows two different ways of requiring that two vectors in a struct have the same length
// The first method uses an internal specification, which translates nicely to flux rust with pure values
// The second method uses a ghost variable in the struct

#![feature(register_tool)]
#![register_tool(flux)]

mod rvec;
use rvec::RVec;

//#[flux::ty(struct<l: int{0 <= l}>{a: RVec<T>@l, b: RVec<U>@l})]
struct Internal<T, U> {
    a: RVec<T>,
    b: RVec<U>,
}

fn _construct_internal() -> Internal<i32, i32> {
    // This should work
    let mut vec1 = RVec::new();
    vec1.push(1);
    vec1.push(2);
    vec1.push(3);
    let mut vec2 = RVec::new();
    vec2.push(1);
    vec2.push(2);
    vec2.push(3);

    Internal { a: vec1, b: vec2 }
    // But this shouldn't
    /*vec2.push(4)
    Internal {
        a: vec1,
        b: vec2,
    }*/
}

fn _use_internal(mut internal: Internal<i32, i32>) -> i32 {
    // This should be safe, because of the invariant
    if internal.a.len() > 1 {
        *internal.b.get_mut(1)
    } else {
        0
    }
}

//#[flux::ty(struct<l: int{0 <= l}, l2: int{0 <= l2>}>{ga: RVec<T>@l, gb: RVec<U>@l2, ginv: (){v: l == l2}})]
struct Ghost<T, U> {
    ga: RVec<T>,
    gb: RVec<U>,
    ginv: (),
}

fn _construct_ghost() -> Ghost<i32, i32> {
    let mut vec1 = RVec::new();
    vec1.push(1);
    vec1.push(2);
    vec1.push(3);
    let mut vec2 = RVec::new();
    vec2.push(1);
    vec2.push(2);
    vec2.push(3);

    // This should work
    Ghost { ga: vec1, gb: vec2, ginv: () }
    // But this shouldn't
    /*vec2.push(4);
    Ghost {
        ga: vec1,
        gb: vec2,
        ginv: (),
    }*/
}

fn _use_ghost(mut ghost: Ghost<i32, i32>) -> i32 {
    // This should be safe, because of the invariant
    if ghost.ga.len() > 1 {
        *ghost.gb.get_mut(1)
    } else {
        0
    }
}
