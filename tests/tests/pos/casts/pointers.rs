pub fn foo(z: usize) {
    let _boo = z as *const u8;
}
#[flux::spec(fn(*mut [@ptr] T) -> *const [ptr] T)]
fn mut_to_const_ptr<T>(ptr: *mut T) -> *const T {
    ptr
}
#[flux::spec(fn(*const [@ptr] T) -> *mut [ptr] T)]
fn const_to_mut_ptr<T>(ptr: *const T) -> *mut T {
    ptr as *mut T
}
