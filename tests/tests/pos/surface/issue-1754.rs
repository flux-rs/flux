pub struct Token<T>(*mut T);

pub fn spawn<F>(_future: impl FnOnce() -> F) -> Token<impl Sized> {
    Token(std::ptr::null_mut::<F>())
}
