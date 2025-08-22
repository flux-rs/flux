use flux_rs::attrs::*;

pub enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

#[flux::specs {

    #[refined_by(n: int)]
    #[invariant(n >= 0)]
    enum List<T> {
      Nil                       -> List<T>[0],
      Cons(T, Box<List<T>[@n]>) -> List<T>[n+1],
    }

    fn nil<T>() -> List<T>[0];

    fn cons<T>(h: T, tl: List<T>[@n]) -> List<T>[n+1];


}]
const _: () = ();

pub fn nil<T>() -> List<T> {
    List::Nil
}

pub fn cons<T>(h: T, tl: List<T>) -> List<T> {
    List::Cons(h, Box::new(tl))
}

#[spec(fn mk_list(n: usize) -> List<usize>[n])]
pub fn mk_list(n: usize) -> List<usize> {
    if n == 0 { nil() } else { cons(n, mk_list(n - 1)) }
}

#[spec(fn(&List<T>[@n]) -> usize[n])]
pub fn len<T>(l: &List<T>) -> usize {
    match l {
        List::Nil => 0,
        List::Cons(_, l) => 1 + len(l),
    }
}
