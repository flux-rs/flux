//! Self ty alias in trait implementation

trait Trait {
    fn some_fun() -> Self;
}

impl Trait for i32 {
    fn some_fun() -> Self {
        0
    }
}
