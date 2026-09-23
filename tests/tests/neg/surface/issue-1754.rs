pub struct Wrap<T>(T);
pub struct Token<T>(*mut T);

#[flux::spec(fn() -> Wrap<impl Iterator<Item = i32{v: v != 67}>>)]
pub fn test_return_impl_bad() -> Wrap<impl Iterator<Item = i32>> {
    Wrap(Some(67).into_iter()) //~ ERROR refinement type
}

#[flux::spec(fn() -> Token<impl Iterator<Item = i32{v: v < 5 || v > 50}>>)]
pub fn test_return_impl_ptr_bad() -> Token<impl Iterator<Item = i32>> {
    Token(Box::into_raw(Box::new(Some(23).into_iter()))) //~ ERROR refinement type
}
