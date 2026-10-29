//@no-prefer-dynamic

pub struct Wrapper(pub i32);

pub trait Get {
    fn get(self) -> i32;
}

// The self type has an anonymous lifetime, which cannot be named in an extern spec
impl Get for &Wrapper {
    fn get(self) -> i32 {
        self.0
    }
}
