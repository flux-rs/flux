struct S1<T1, T2> {
    x: T1,
    y: T2,
}

impl<T1, T2> S1<T1, T2> {
    #[flux::sig(fn(&S1))] //~ ERROR this struct takes 2 generic argument
    fn test(&self) {}
}

type S2<T> = S1<T, T>;

// wrong number of generic arguments for alias
#[flux::sig(fn(x: S2<i64, i32>) -> i64)] //~ ERROR this type alias takes 1 generic argument but 2 generic arguments were supplied
fn test01(x: S2<i32>) -> i64 {
    0
}
