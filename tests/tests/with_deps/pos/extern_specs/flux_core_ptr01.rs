extern crate flux_core;

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && addr > 0 && size >= 8 && addr % 4 == 0}))]
pub fn test_add_ex(ptr: *const i32) {
    unsafe {
        let _val0 = std::ptr::read(ptr.add(0));
        let _val1 = std::ptr::read(ptr.add(1));
    }
}

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && addr > 0 && size == 8 && addr % 4 == 0}))]
pub fn test_add_ix(ptr: *const i32) {
    unsafe {
        let _val0 = std::ptr::read(ptr.add(0));
        let _val1 = std::ptr::read(ptr.add(1));
    }
}

#[flux::spec(fn (ptr: {*mut[@base, @addr, @size] i32 | addr >= base && addr > 0 && size >= 8 && addr % 4 == 0}))]
pub fn test_add_mut_ex(ptr: *mut i32) {
    unsafe {
        std::ptr::write(ptr.add(0), 10);
        std::ptr::write(ptr.add(1), 20);
    }
}

#[flux::spec(fn (ptr: {*mut[@base, @addr, @size] i32 | addr >= base && addr > 0 && size == 8 && addr % 4 == 0}))]
pub fn test_add_mut_ix(ptr: *mut i32) {
    unsafe {
        std::ptr::write(ptr.add(0), 10);
        std::ptr::write(ptr.add(1), 20);
    }
}

// --- offset (signed count — forward and backward) ---

// forward: like add(1) but with isize
#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && addr > 0 && size >= 8 && addr % 4 == 0}))]
pub fn test_offset_forward(ptr: *const i32) {
    unsafe {
        let _val0 = std::ptr::read(ptr.offset(0));
        let _val1 = std::ptr::read(ptr.offset(1));
    }
}

// backward: ptr is one element into its allocation; offset(-1) steps back to base
// After offset(-1): new addr = addr - 4, new size = size + 4. Read requires size + 4 >= 4,
// i.e. size >= 0. Non-null requires addr - 4 > 0, i.e. addr > 4.
#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr > 4 && addr >= base + 4 && size >= 0 && addr % 4 == 0}))]
pub fn test_offset_backward(ptr: *const i32) {
    unsafe {
        let _ = std::ptr::read(ptr.offset(-1));
    }
}

// *mut T forward: offset + write
#[flux::spec(fn (ptr: {*mut[@base, @addr, @size] i32 | addr >= base && addr > 0 && size >= 8 && addr % 4 == 0}))]
pub fn test_offset_mut_forward(ptr: *mut i32) {
    unsafe {
        std::ptr::write(ptr.offset(0), 10);
        std::ptr::write(ptr.offset(1), 20);
    }
}

// *mut T backward
#[flux::spec(fn (ptr: {*mut[@base, @addr, @size] i32 | addr > 4 && addr >= base + 4 && size >= 0 && addr % 4 == 0}))]
pub fn test_offset_mut_backward(ptr: *mut i32) {
    unsafe {
        std::ptr::write(ptr.offset(-1), 42);
    }
}
