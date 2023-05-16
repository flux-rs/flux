#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(i32{v: false}) -> T)]
pub fn never<T>(_: i32) -> T {
    loop {}
}

/// (i32) lists indexed by the _set_ of elements.

#[flux::refined_by(elems: Set<int>)]
pub enum List {
    #[flux::variant(List[{}])]
    Nil,
    #[flux::variant((i32[@n], List[@elems]) -> List[set_add(n, elems)])]
    Cons(i32, Box<List>)
}

#[flux::sig(fn(&List[@xs]) -> bool[set_emp(xs)])]
pub fn is_empty(l: &List) -> bool {
    match l {
        List::Nil => true,
        List::Cons(_, _) => false,
    }
}


#[flux::sig(fn({&List[@xs] | !set_emp(xs)}) -> i32)]
pub fn head(l: &List) -> i32 {
    match l {
        List::Nil => never(0),
        List::Cons(h, _) => *h,
    }
}

#[flux::sig(fn({&List[@xs] | !set_emp(xs)}) -> &List)]
pub fn tail(l: &List) -> &List {
    match l {
        List::Nil => never(0),
        List::Cons(_, t) => t,
    }
}

#[flux::sig(fn(val: i32, n: usize) -> List[set_sng(val)])]
pub fn clone(val: i32, n: usize) -> List {
    if n == 0 {
        List::Nil
    } else {
        List::Cons(val, Box::new(clone(val, n - 1)))
    }
}

#[flux::sig(fn(List[@xs1], List[@xs2]) -> List[set_union(xs1, xs2)])]
pub fn append(l1: List, l2: List) -> List {
    match l1 {
        List::Nil => l2,
        List::Cons(h1, t1) => List::Cons(h1, Box::new(append(*t1, l2))),
    }
}

#[flux::sig(fn(k:i32, &List[@xs]) -> bool[set_mem(k, xs)])]
pub fn mem(k:i32, l: &List) -> bool {
    match l {
        List::Cons(h, tl) => {
            if k == h {
                true
            } else {
                mem(k, tl)
            }
        }
        List::Nil => false,
    }
}
