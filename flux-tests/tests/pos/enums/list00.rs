#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(i32{v:false}) -> T)]
pub fn never<T>(_x: i32) -> T {
    loop {}
}

#[flux::refined_by(n:int)]
#[flux::invariant(n >= 0)]
pub enum List {
    #[flux::variant(List[0])]
    Nil,
    #[flux::variant({i32, Box<List[@n]>} -> List[n+1])]
    Cons(i32, Box<List>),
}

#[flux::sig(fn(&List[@n]) -> bool[n == 0])]
pub fn empty(l: &List) -> bool {
    match l {
        List::Nil => true,
        List::Cons(_, _) => false,
    }
}

#[flux::sig(fn(&List[@n]) -> i32[n])]
pub fn len(l: &List) -> i32 {
    match l {
        List::Nil => 0,
        List::Cons(_, tl) => 1 + len(tl),
    }
}

#[flux::sig(fn({&List[@n] : 0 < n}) -> i32)]
pub fn head(l: &List) -> i32 {
    match l {
        List::Nil => never(0),
        List::Cons(h, _) => *h,
    }
}

#[flux::sig(fn({&List[@n] : 0 < n}) -> &List)]
pub fn tail(l: &List) -> &List {
    match l {
        List::Nil => never(0),
        List::Cons(_, t) => t,
    }
}

#[flux::sig(fn(i32, n:usize) -> List[n])]
pub fn clone(val: i32, n: usize) -> List {
    if n == 0 {
        List::Nil
    } else {
        List::Cons(val, Box::new(clone(val, n - 1)))
    }
}

#[flux::sig(fn(List[@n1], List[@n2]) -> List[n1+n2])]
pub fn append(l1: List, l2: List) -> List {
    match l1 {
        List::Nil => l2,
        List::Cons(h1, t1) => List::Cons(h1, Box::new(append(*t1, l2))),
    }
}

#[flux::sig(fn(&List[@n], k:usize{k < n} ) -> i32)]
pub fn get_nth(l: &List, k: usize) -> i32 {
    match l {
        List::Cons(h, tl) => {
            if k == 0 {
                *h
            } else {
                get_nth(tl, k - 1)
            }
        }
        List::Nil => never(0),
    }
}
