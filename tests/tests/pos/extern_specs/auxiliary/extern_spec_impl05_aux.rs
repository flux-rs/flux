//@no-prefer-dynamic

pub struct Wrapper(pub i32);

// The impl header has an anonymous lifetime, which cannot be named in an extern spec
impl From<&i32> for Wrapper {
    fn from(x: &i32) -> Wrapper {
        Wrapper(*x)
    }
}
