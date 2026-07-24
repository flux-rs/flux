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
    #[flux::variant({i32[@n], Box<List[@elems]>} -> List[set_add(n, elems)])]
    Cons { head: i32, tail: Box<List> },
}

#[flux::sig(fn(&List[@xs]) -> bool[xs == set_emp()])]
pub fn is_empty(l: &List) -> bool {
    match l {
        List::Nil => true,
        List::Cons { .. } => false,
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
        List::Cons { head, .. } => *head,
    }
}

#[flux::sig(fn({&List[@xs] | !set_is_empty(xs)}) -> &List)]
pub fn tail(l: &List) -> &List {
    match l {
        List::Nil => unreachable(),
        List::Cons { tail, .. } => tail,
    }
}

#[flux::sig(fn(List[@xs1], List[@xs2]) -> List[set_union(xs1.elems, xs2.elems)])]
pub fn append(l1: List, l2: List) -> List {
    match l1 {
        List::Nil => l2,
        List::Cons { head, tail } => List::Cons { head, tail: Box::new(append(*tail, l2)) },
    }
}

// Silly function, but to get it working with &List we need to memoize the
// unfolding, as other we get three unfoldings with different names which is
// ok for int but not for Set.
#[flux::sig(fn(k:i32, List[@xs]) -> bool[set_is_in(k, xs.elems)])]
pub fn mem(k: i32, l: List) -> bool {
    match l {
        List::Cons { head, tail } => {
            if k == head {
                true
            } else {
                mem(k, *tail)
            }
        }
        List::Nil => false,
    }
}
