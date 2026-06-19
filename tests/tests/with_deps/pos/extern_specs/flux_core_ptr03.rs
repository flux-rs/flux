extern crate flux_core;

// --- sub ---

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && addr > 0 && size >= 8 && addr % 4 == 0}))]
pub fn test_sub_ex(ptr: *const i32) {
    unsafe {
        let ptr1 = ptr.add(1);
        let ptr0 = ptr1.sub(1);
        let _val = std::ptr::read(ptr0);
    }
}

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && addr > 0 && size == 8 && addr % 4 == 0}))]
pub fn test_sub_ix(ptr: *const i32) {
    unsafe {
        let ptr1 = ptr.add(1);
        let ptr0 = ptr1.sub(1);
        let _val = std::ptr::read(ptr0);
    }
}

// --- byte_add ---

pub fn test_byte_add(buf: &mut [i32; 2]) {
    let ptr = buf.as_mut_ptr();
    unsafe {
        std::ptr::write(ptr.byte_add(0), 10);
        std::ptr::write(ptr.byte_add(4), 20);
    }
}

// --- byte_sub ---

pub fn test_byte_sub(buf: &mut [i32; 2]) {
    let ptr = buf.as_mut_ptr();
    unsafe {
        let ptr1 = ptr.byte_add(4);
        let ptr0 = ptr1.byte_sub(4);
        std::ptr::write(ptr0, 10);
        std::ptr::write(ptr1, 20);
    }
}

// --- byte_offset (signed count — forward and backward) ---

// forward: byte_offset(4) advances by 4 bytes to the second element
pub fn test_byte_offset_forward(buf: &mut [i32; 2]) {
    let ptr = buf.as_mut_ptr();
    unsafe {
        std::ptr::write(ptr.byte_offset(0), 10);
        std::ptr::write(ptr.byte_offset(4), 20);
    }
}

// backward: advance then step back; reads both elements
pub fn test_byte_offset_backward(buf: &mut [i32; 2]) {
    let ptr = buf.as_mut_ptr();
    unsafe {
        let ptr1 = ptr.byte_add(4);
        let ptr0 = ptr1.byte_offset(-4);
        std::ptr::write(ptr0, 10);
        std::ptr::write(ptr1, 20);
    }
}
