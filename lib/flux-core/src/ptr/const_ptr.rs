use flux_attrs::*;

#[extern_spec(core::ptr)]
impl<T> *const T {
    #[spec(fn (me: *const[@src] T, count: usize) -> *const{p: ptr_size(p) == ptr_size(src) - count} T)]
    unsafe fn add(self, count: usize) -> Self;
}
