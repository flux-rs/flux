#[flux::sig(fn(i32{v:false}) -> T)]
pub fn never<T>(_x: i32) -> T {
    loop {}
}

#[derive(Debug)]
pub enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

pub fn len<T>(l: &List<T>) -> i32 {
    match l {
        List::Nil => 0,
        List::Cons(_, tl) => 1 + len(&*tl),
    }
}

pub fn head<T>(l: &List<T>) -> &T {
    match l {
        List::Nil => never(0),
        List::Cons(h, _) => h,
    }
}

pub fn tail<T>(l: &List<T>) -> &List<T> {
    match l {
        List::Nil => never(0),
        List::Cons(_, t) => &*t,
    }
}

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
