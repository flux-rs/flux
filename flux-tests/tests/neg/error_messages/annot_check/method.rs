#![feature(register_tool)]
#![register_tool(flux)]

struct S<T> {
    x: T,
}

impl<T> S<T> {
    #[flux::sig(fn(&S))] //~ ERROR this struct must take 1 generic argument
    fn test(&self) {}
}
