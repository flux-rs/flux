use flux_attrs::*;

#[extern_spec(core::ptr)]
impl<T> *mut T {
    #[spec(fn (me: *mut [@size] T, count: usize) -> *mut[size - count] T)]
    unsafe fn add(self, count: usize) -> Self;
}
