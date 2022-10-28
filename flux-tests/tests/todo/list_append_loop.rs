#![feature(register_tool, box_patterns)]
#![register_tool(flux)]

#[flux::refined_by(len: int)]
enum List<T> {
    #[flux::variant(List<T>[0])]
    Nil,
    #[flux::variant((T, Box<List<T>[@n]>) -> List<T>[n + 1])]
    Cons(T, Box<List<T>>),
}

// Panics when joining environments because we are closing a box with an outstanding
// ptr(mut) to the box's location, i.e.,
// we start with
//   r1: box(a0), r2: ptr(mut, a0), a0: T,
// and closing the box produces
//   r1: Box<T>, r2: ptr(mut, a0)
//
// after closing the box we should have
//   r1: Box<T>, r2: &mut T
//
impl List<T> {
    #[flux::sig(fn(self: &strg List<T>[@n], List<T>[@m]) ensures self: List<T>[n + m])]
    fn append(&mut self, other: List<T>) {
        let mut cur = self;
        while let List::Cons(_, tl) = cur {
            cur = tl;
        }
        *cur = other;
    }
}
