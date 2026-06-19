extern crate flux_core;

// --- add ---

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && size > 8 && addr != 0 && addr % 4 == 0}))]
pub fn test_add_ex(ptr: *const i32) {
    unsafe {
        let _val0 = std::ptr::read(ptr.add(0));
        let _val1 = std::ptr::read(ptr.add(1)); //~ ERROR refinement type error
        let _val2 = std::ptr::read(ptr.add(2)); //~ ERROR refinement type error
    }
}

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && size == 8 && addr != 0 && addr % 4 == 0}))]
pub fn test_add_ix(ptr: *const i32) {
    unsafe {
        let _val0 = std::ptr::read(ptr.add(0));
        let _val1 = std::ptr::read(ptr.add(1)); //~ ERROR refinement type error
        let _val2 = std::ptr::read(ptr.add(2)); //~ ERROR refinement type error
    }
}

#[flux::spec(fn (ptr: {*mut[@base, @addr, @size] i32 | addr >= base && size > 8 && addr != 0 && addr % 4 == 0}))]
pub fn test_add_mut_ex(ptr: *mut i32) {
    unsafe {
        std::ptr::write(ptr.add(0), 10);
        std::ptr::write(ptr.add(1), 20); //~ ERROR refinement type error
        std::ptr::write(ptr.add(2), 30); //~ ERROR refinement type error
    }
}

#[flux::spec(fn (ptr: {*mut[@base, @addr, @size] i32 | addr >= base && size == 8 && addr != 0 && addr % 4 == 0}))]
pub fn test_add_mut_ix(ptr: *mut i32) {
    unsafe {
        std::ptr::write(ptr.add(0), 10);
        std::ptr::write(ptr.add(1), 20); //~ ERROR refinement type error
        std::ptr::write(ptr.add(2), 30); //~ ERROR refinement type error
    }
}

// --- offset (signed count) ---

// forward offset past end: size == 4 holds only one i32; offset(2) needs 8 bytes
#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && addr > 0 && size == 4 && addr % 4 == 0}))]
pub fn test_offset_forward_too_far(ptr: *const i32) {
    unsafe {
        let _ = ptr.offset(2); //~ ERROR refinement type error
    }
}

// backward offset before base: addr == base means no room behind the pointer
#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr == base && size >= 4 && addr % 4 == 0}))]
pub fn test_offset_backward_past_base(ptr: *const i32) {
    unsafe {
        let _ = ptr.offset(-1); //~ ERROR refinement type error
    }
}
