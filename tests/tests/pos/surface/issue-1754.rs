pub struct Token<T>(*mut T);
pub struct Wrap<T>(T);

pub fn spawn<F>(_future: impl FnOnce() -> F) -> Token<impl Sized> {
    Token(std::ptr::null_mut::<F>())
}

#[flux::spec(fn() -> Wrap<impl Iterator<Item = i32[123]>>)]
pub fn test_return_impl() -> Wrap<impl Iterator<Item = i32>> {
    Wrap(Some(123).into_iter())
}

#[flux::spec(fn() -> Token<impl Iterator<Item = i32{v:1 <= v}>>)]
pub fn test_return_impl_ptr() -> Token<impl Iterator<Item = i32>> {
    Token(Box::into_raw(Box::new(Some(22).into_iter())))
}
