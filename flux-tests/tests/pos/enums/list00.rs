#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn(i32{v:false}) -> T)]
pub fn never<T>(_x: i32) -> T {
    loop {}
}

#[flux::refined_by(n:int)]
pub enum List {
    #[flux::variant(List[0])]
    Nil,
    #[flux::variant({i32, Box<List[@n]>} -> List[n+1])]
    Cons(i32, Box<List>),
}

#[flux::sig(fn({&List[@n] : 0 <= n}) -> bool[n == 0])]
pub fn empty(l: &List) -> bool {
    match l {
        List::Nil => true,
        List::Cons(_, _) => false,
    }
}

#[flux::sig(fn(&List[n]) -> i32[n])]
pub fn len(l: &List) -> i32 {
    match l {
        List::Nil => 0,
        List::Cons(_, tl) => 1 + len(tl),
    }
}

#[flux::sig(fn ({&List[@n] : 0 < n}) -> i32)]
pub fn head(l: &List) -> i32 {
    match l {
        List::Nil => never(0),
        List::Cons(h, _) => *h,
    }
}

// TODO(RJ): fix this odd parse non-error -- silently accepted?!
// #[flux::sig(fn ({&List<[@n] : 0 < n}) -> &List)]
//                       ^???

#[flux::sig(fn ({&List[@n] : 0 < n}) -> &List)]
pub fn tail(l: &List) -> &List {
    match l {
        List::Nil => never(0),
        List::Cons(_, t) => t,
    }
}

/*
pub fn clone(val: i32, n: usize) -> List<i32> {
    if n <= 0 {
        List::Nil
    } else {
        List::Cons(val, Box::new(clone(val, n - 1)))
    }
}

pub fn append<T>(l1: List<T>, l2: List<T>) -> List<T> {
    match l1 {
        List::Nil => l2,
        List::Cons(h1, t1) => List::Cons(h1, Box::new(append(*t1, l2))),
    }
}

pub fn get_nth<T>(l: &List<T>, n: usize) -> &T {
    match l {
        List::Cons(h, tl) => {
            if n == 0 {
                h
            } else {
                get_nth(&*tl, n - 1)
            }
        }
        List::Nil => never(0),
    }
}

pub fn list_test(val: i32, size: usize) {
    if 10 < size {
        let l = clone(val, size);
        let _v = get_nth(&l, 5);
        // assert(v == val);
    }
}
*/
