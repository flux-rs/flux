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
        List::Cons(_, _) => true, //~ ERROR refinement type
    }
}

#[flux::sig(fn(&List[@n]) -> i32[n])]
pub fn len(l: &List) -> i32 {
    match l {
        List::Nil => 0,
        List::Cons(_, tl) => len(tl), //~ ERROR refinement type
    }
}

#[flux::sig(fn(&List[@n]) -> i32)]
pub fn head(l: &List) -> i32 {
    match l {
        List::Nil => never(0), //~ ERROR refinement type
        List::Cons(h, _) => *h,
    }
}

#[flux::sig(fn(List[@n1], List[@n2]) -> List[n2])]
pub fn append(l1: List, l2: List) -> List {
    match l1 {
        List::Nil => l2,
        List::Cons(h1, t1) => List::Cons(h1, Box::new(append(*t1, l2))),
    }
} //~ ERROR refinement type

#[flux::sig(fn(&List[@n], k:usize{k <= n} ) -> i32)]
pub fn get_nth(l: &List, k: usize) -> i32 {
    match l {
        List::Cons(h, tl) => {
            if k == 0 {
                *h
            } else {
                get_nth(tl, k - 1)
            }
        }
        List::Nil => never(0), //~ ERROR refinement type
    }
}
