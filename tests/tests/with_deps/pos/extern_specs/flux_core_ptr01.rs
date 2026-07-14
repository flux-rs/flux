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

// --- offset_from (returns element-count distance between same-allocation pointers) ---
use flux_rs::assert;

// forward distance: ptr.add(3) is 2 elements ahead of ptr.add(1)
pub fn test_offset_from_pos(buf: &[i32; 4]) {
    let ptr = buf.as_ptr();
    unsafe {
        let p1 = ptr.add(1);
        let p2 = ptr.add(3);
        let diff = p2.offset_from(p1);
        assert(diff == 2);
    }
}

// negative distance: p1 ahead of p2, result is negative
pub fn test_offset_from_neg(buf: &[i32; 4]) {
    let ptr = buf.as_ptr();
    unsafe {
        let p1 = ptr.add(3);
        let p2 = ptr.add(1);
        let diff = p2.offset_from(p1);
        assert(diff == -2);
    }
}

// self offset_from self == 0
pub fn test_offset_from_zero(buf: &[i32; 4]) {
    let ptr = buf.as_ptr();
    unsafe {
        let p = ptr.add(2);
        let diff = p.offset_from(p);
        assert(diff == 0);
    }
}

// *mut T: offset_from takes *const T as origin (implicit *mut → *const coercion)
pub fn test_offset_from_mut(buf: &mut [i32; 4]) {
    let ptr = buf.as_mut_ptr();
    unsafe {
        let p1 = ptr.add(1);
        let p2 = ptr.add(3);
        let diff = p2.offset_from(p1);
        assert(diff == 2);
    }
}

// --- offset_from_unsigned ---

// forward distance: returns usize, same arithmetic as offset_from for self >= origin
pub fn test_offset_from_unsigned_pos(buf: &[i32; 4]) {
    let ptr = buf.as_ptr();
    unsafe {
        let p1 = ptr.add(1);
        let p2 = ptr.add(3);
        let diff = p2.offset_from_unsigned(p1);
        assert(diff == 2);
    }
}

// self == origin: distance is zero
pub fn test_offset_from_unsigned_zero(buf: &[i32; 4]) {
    let ptr = buf.as_ptr();
    unsafe {
        let p = ptr.add(2);
        let diff = p.offset_from_unsigned(p);
        assert(diff == 0);
    }
}

// offset_from_unsigned inverts add: p.add(n).offset_from_unsigned(p) == n
pub fn test_offset_from_unsigned_roundtrip(buf: &[i32; 4]) {
    let ptr = buf.as_ptr();
    unsafe {
        let p2 = ptr.add(2);
        assert(p2.offset_from_unsigned(ptr) == 2);
    }
}

// *mut T case
pub fn test_offset_from_unsigned_mut(buf: &mut [i32; 4]) {
    let ptr = buf.as_mut_ptr();
    unsafe {
        let p1 = ptr.add(1);
        let p2 = ptr.add(3);
        let diff = p2.offset_from_unsigned(p1);
        assert(diff == 2);
    }
}


pub fn ref_to_ptr_read(z: i32) -> i32 {
    unsafe { std::ptr::read(&z) }
}
