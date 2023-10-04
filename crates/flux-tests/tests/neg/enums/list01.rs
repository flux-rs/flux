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

#[flux::sig(fn() -> T requires false)]
pub fn unreachable<T>() -> T {
    unreachable!()
}

pub fn head(l: &List) -> i32 {
    match l {
        List::Nil => unreachable(), //~ ERROR refinement type
        List::Cons(h, _) => *h,
    }
}

pub fn tail(l: &List) -> &List {
    match l {
        List::Nil => unreachable(), //~ ERROR refinement type
        List::Cons(_, t) => t,
    }
}
