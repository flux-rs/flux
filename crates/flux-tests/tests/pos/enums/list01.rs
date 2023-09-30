// #![feature(register_tool)]
// #![register_tool(flux)]
// #![feature(custom_inner_attributes)]
#![flux::defs {
    fn set_add(x: int, s: Set<int>) -> Set<int> { set_union(set_singleton(x), s) }
    fn set_is_empty(s: Set<int>) -> bool { s == set_empty(0) }
    fn set_emp() -> Set<int> { set_empty(0) }
}]

/// (i32) lists indexed by the _set_ of elements.

#[flux::refined_by(elems: Set<int>)]
pub enum List {
    #[flux::variant(List[set_emp()])]
    Nil,
    #[flux::variant((i32[@n], Box<List[@elems]>) -> List[set_add(n, elems)])]
    Cons(i32, Box<List>),
}

#[flux::sig(fn(&List[@xs]) -> bool[xs == set_emp()])]
pub fn is_empty(l: &List) -> bool {
    match l {
        List::Nil => true,
        List::Cons(_, _) => false,
    }
}

#[flux::sig(fn () -> List[set_emp()])]
pub fn null() -> List {
    List::Nil
}

#[flux::sig(fn() -> T requires false)]
pub fn unreachable<T>() -> T {
    unreachable!()
}

#[flux::sig(fn({&List[@xs] | !set_is_empty(xs)}) -> i32)]
pub fn head(l: &List) -> i32 {
    match l {
        List::Nil => unreachable(),
        List::Cons(h, _) => *h,
    }
}

#[flux::sig(fn({&List[@xs] | !set_is_empty(xs)}) -> &List)]
pub fn tail(l: &List) -> &List {
    match l {
        List::Nil => unreachable(),
        List::Cons(_, t) => t,
    }
}

#[flux::sig(fn(List[@xs1], List[@xs2]) -> List[set_union(xs1, xs2)])]
pub fn append(l1: List, l2: List) -> List {
    match l1 {
        List::Nil => l2,
        List::Cons(h1, t1) => List::Cons(h1, Box::new(append(*t1, l2))),
    }
}

// Silly function, but to get it working with &List we need to memoize the
// unfolding, as other we get three unfoldings with different names which is
// ok for int but not for Set.
#[flux::sig(fn(k:i32, List[@xs]) -> bool[set_is_in(k, xs)])]
pub fn mem(k: i32, l: List) -> bool {
    match l {
        List::Cons(h, tl) => {
            if k == h {
                true
            } else {
                mem(k, *tl)
            }
        }
        List::Nil => false,
    }
}
