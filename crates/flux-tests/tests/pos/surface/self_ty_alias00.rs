#[flux::refined_by(n: int)]
struct S<T> {
    #[flux::field(i32[@n])]
    f1: i32,
    f2: T,
}

impl<T> S<T> {
    #[flux::sig(fn(&Self[@n]) -> i32[n])]
    fn test1(&self) -> i32 {
        self.f1
    }
}

impl S<i32> {
    #[flux::sig(fn(&Self) -> i32)]
    fn test2(&self) -> i32 {
        self.f2
    }
}
