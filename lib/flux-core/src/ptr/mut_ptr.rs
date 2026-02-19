use flux_attrs::*;

#[extern_spec(core::ptr)]
impl<T> *mut T {
    #[spec(fn (me: *mut [@src] T, count: usize) -> *mut{p: ptr_size(p) == ptr_size(src) - count} T)]
    unsafe fn add(self, count: usize) -> Self;
}
