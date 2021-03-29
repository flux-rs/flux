#![feature(register_tool)]
#![register_tool(liquid)]

#[liquid::measure("fn addr(*const int) -> int")]
#[liquid::measure("fn len(*const int) -> int")]
mod array {
    #[liquid::assume("fn(n: int) -> {p: *const bool | addr(p) == 0 && len(p) == n}")]
    pub fn alloc(len: usize) -> *const bool {
        let layout = std::alloc::Layout::from_size_align(len, 1).unwrap();
        let ptr = unsafe { std::alloc::alloc_zeroed(layout) };

        if ptr.is_null() {
            panic!("Out of memory");
        }

        ptr as *const bool
    }

    #[liquid::assume("fn(p: *const bool, n: int) -> {q: *const bool | addr(q) == addr(p) + n && len(q) == len(p)}")]
    fn add_ptr(ptr: *const bool, offset: usize) -> *const bool {
        (ptr as usize + offset) as *const bool
    }

    #[liquid::assume("fn(p: { *const bool | addr(p) < len(p) }) -> bool")]
    unsafe fn deref_ptr(ptr: *const bool) -> bool {
        *ptr
    }

    #[liquid::ty("fn(p: *const bool , i: { int | i + addr(p) < len(p) })")]
    pub unsafe fn get(ptr: *const bool, index: usize) -> bool {
        let new_ptr = add_ptr(ptr, index);
        deref_ptr(new_ptr)
    }
}

#[liquid::ty("fn() -> bool")]
fn legal_access() -> bool {
    let array = array::alloc(10);
    unsafe { array::get(array, 9) }
}
