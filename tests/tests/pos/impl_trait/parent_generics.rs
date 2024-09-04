fn test00<T>(x: T) -> impl FnOnce(i32) -> i32 {
    |z: i32| z
}

struct S<T> {
    pub value: Option<T>,
}

impl<T> S<T> {
    pub fn method00(&self) -> impl FnOnce(i32) -> i32 {
        |z: i32| z
    }
}
