extern crate flux_core;

use std::ptr::NonNull;

// --- add ---

#[flux::spec(fn (nn: NonNull<i32>[@base, @addr, @size]) requires addr >= base && addr > 0 && size >= 8 && addr % 4 == 0)]
pub fn test_add_ex(nn: NonNull<i32>) {
    unsafe {
        let _val0 = std::ptr::read(nn.add(0).as_ptr());
        let _val1 = std::ptr::read(nn.add(1).as_ptr());
    }
}

#[flux::spec(fn (nn: NonNull<i32>[@base, @addr, @size]) requires addr >= base && addr > 0 && size == 8 && addr % 4 == 0)]
pub fn test_add_ix(nn: NonNull<i32>) {
    unsafe {
        let _val0 = std::ptr::read(nn.add(0).as_ptr());
        let _val1 = std::ptr::read(nn.add(1).as_ptr());
    }
}

#[flux::spec(fn (nn: NonNull<i32>[@base, @addr, @size]) requires addr >= base && addr > 0 && size >= 8 && addr % 4 == 0)]
pub fn test_add_mut_ex(nn: NonNull<i32>) {
    unsafe {
        std::ptr::write(nn.add(0).as_ptr(), 10);
        std::ptr::write(nn.add(1).as_ptr(), 20);
    }
}

#[flux::spec(fn (nn: NonNull<i32>[@base, @addr, @size]) requires addr >= base && addr > 0 && size == 8 && addr % 4 == 0)]
pub fn test_add_mut_ix(nn: NonNull<i32>) {
    unsafe {
        std::ptr::write(nn.add(0).as_ptr(), 10);
        std::ptr::write(nn.add(1).as_ptr(), 20);
    }
}

// --- sub ---

#[flux::spec(fn (nn: NonNull<i32>[@base, @addr, @size]) requires addr >= base && addr > 0 && size >= 8 && addr % 4 == 0)]
pub fn test_sub_ex(nn: NonNull<i32>) {
    unsafe {
        let nn1 = nn.add(1);
        let nn0 = nn1.sub(1);
        let _val = std::ptr::read(nn0.as_ptr());
    }
}

#[flux::spec(fn (nn: NonNull<i32>[@base, @addr, @size]) requires addr >= base && addr > 0 && size == 8 && addr % 4 == 0)]
pub fn test_sub_ix(nn: NonNull<i32>) {
    unsafe {
        let nn1 = nn.add(1);
        let nn0 = nn1.sub(1);
        let _val = std::ptr::read(nn0.as_ptr());
    }
}

// --- offset (signed count — forward and backward) ---

// forward: like add(1) but with isize
#[flux::spec(fn (nn: NonNull<i32>[@base, @addr, @size]) requires addr >= base && addr > 0 && size >= 8 && addr % 4 == 0)]
pub fn test_offset_forward(nn: NonNull<i32>) {
    unsafe {
        let _val0 = std::ptr::read(nn.offset(0).as_ptr());
        let _val1 = std::ptr::read(nn.offset(1).as_ptr());
    }
}

// backward: nn is one element into its allocation; offset(-1) steps back to base.
// After offset(-1): new addr = addr - 4, new size = size + 4. Read requires size + 4 >= 4,
// i.e. size >= 0. Non-null requires addr - 4 > 0, i.e. addr > 4.
#[flux::spec(fn (nn: NonNull<i32>[@base, @addr, @size]) requires addr > 4 && addr >= base + 4 && size >= 0 && addr % 4 == 0)]
pub fn test_offset_backward(nn: NonNull<i32>) {
    unsafe {
        let _ = std::ptr::read(nn.offset(-1).as_ptr());
    }
}

// *mut forward: offset + write
#[flux::spec(fn (nn: NonNull<i32>[@base, @addr, @size]) requires addr >= base && addr > 0 && size >= 8 && addr % 4 == 0)]
pub fn test_offset_mut_forward(nn: NonNull<i32>) {
    unsafe {
        std::ptr::write(nn.offset(0).as_ptr(), 10);
        std::ptr::write(nn.offset(1).as_ptr(), 20);
    }
}

// *mut backward
#[flux::spec(fn (nn: NonNull<i32>[@base, @addr, @size]) requires addr > 4 && addr >= base + 4 && size >= 0 && addr % 4 == 0)]
pub fn test_offset_mut_backward(nn: NonNull<i32>) {
    unsafe {
        std::ptr::write(nn.offset(-1).as_ptr(), 42);
    }
}
