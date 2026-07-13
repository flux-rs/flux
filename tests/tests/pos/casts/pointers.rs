pub fn foo(z: usize) {
    let _boo = z as *const u8;
}

#[flux::spec(fn(*mut [@ptr] T) -> *const [ptr] T)]
fn mut_to_const_ptr<T>(ptr: *mut T) -> *const T {
    ptr
}
