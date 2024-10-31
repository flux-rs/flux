struct S<T> {
    #[flux::field(T{v: v > 0})] //~ ERROR mismatched sorts
    x: T,
}

enum E<T> {
    #[flux::variant((T[@n, @m]) -> E<T>)] //~ ERROR this type takes 1 refinement argument
    A(T),
}

pub trait MyTrait {
    fn foo(&self) -> Self;
}

#[flux::sig(fn(x: T) -> i32[x])] //~ ERROR mismatched sorts
fn generic<T>(x: T) -> i32 {
    0
}
