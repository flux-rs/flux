use flux_attrs::*;

struct S<T> {
    f: T,
}

#[assume_parametric(T)]
impl<T> S<T> {
    #[assume_parametric(T)] //~ WARN `T` is already assumed parametric
    fn get(&self) -> &T {
        &self.f
    }

    #[assume_parametric(U)]
    fn get_with<U>(&self, _: U) -> &T {
        &self.f
    }
}

#[assume_parametric(T)]
trait Id<T> {
    #[assume_parametric(T)] //~ WARN `T` is already assumed parametric
    fn id<'a>(&self, x: &'a T) -> &'a T;
}

#[assume_parametric(T)]
fn free<T>(x: T) -> T {
    x
}

#[spec(fn(&S<i32{v: v > 0}>) -> i32{v: v > 1})]
fn test(x: &S<i32>) -> i32 {
    *x.get() //~ ERROR refinement type error
}
