use flux_attrs::*;

#[extern_spec(core::cell)]
impl<T> UnsafeCell<T> {
    #[assume_parametric(T)]
    #[spec(fn(T) -> UnsafeCell<T>)]
    const fn new(value: T) -> UnsafeCell<T>;
}

#[extern_spec(core::cell)]
impl<T> RefCell<T> {
    #[assume_parametric(T)]
    #[spec(fn(&RefCell<T>) -> RefMut<T>)]
    fn borrow_mut(&self) -> RefMut<'_, T>;
}
