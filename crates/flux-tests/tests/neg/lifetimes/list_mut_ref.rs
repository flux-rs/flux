#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(len: int)]
enum List<'a, T> {
    #[flux::variant(List<T>[0])]
    Nil,
    #[flux::variant((T, &mut List<T>[@n]) -> List<T>[n + 1])]
    Cons(T, &'a mut List<'a, T>),
}

impl<'a, T> List<'a, T> {
    #[flux::sig(fn(&mut List<T>[@n]) -> usize[n])]
    fn len(&mut self) -> usize {
        match self {
            List::Cons(_, tl) => tl.len() + 1,
            List::Nil => 1, //~ ERROR refinement type
        }
    }

    #[flux::sig(fn(&mut List<T>[@n], idx: usize{idx < n}) -> &mut T)]
    fn get_mut(&mut self, idx: usize) -> &mut T {
        match self {
            List::Cons(h, tl) => {
                if idx == 0 {
                    h
                } else {
                    tl.get_mut(idx + 1) //~ ERROR refinement type
                }
            }
            List::Nil => unreachable(),
        }
    }
}

#[flux::sig(fn() -> i32{v : v >= 0})]
fn test() -> i32 {
    let mut nil = List::Nil;
    let mut l1 = List::Cons(0, &mut nil);
    let mut l2 = List::Cons(1, &mut l1);

    *l2.get_mut(0) -= 1;

    *l2.get_mut(1) //~ ERROR refinement type
}

#[flux::sig(fn() -> T requires false)]
fn unreachable<T>() -> T {
    unreachable!()
}
