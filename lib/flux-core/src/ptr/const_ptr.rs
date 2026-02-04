use flux_attrs::*;

#[extern_spec(core::ptr)]
impl<T> *const T {
    #[spec(fn (me: *const[@size] T, count: usize) -> *const[size - count] T)]
    unsafe fn add(self, count: usize) -> Self;
}
