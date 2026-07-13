extern crate flux_core;

use flux_rs::assert;
use std::ptr::NonNull;

// --- offset_from ---

// forward distance: nn.add(3) is 2 elements ahead of nn.add(1)
pub fn test_offset_from_pos(buf: &mut [i32; 4]) {
    let nn = unsafe { NonNull::new_unchecked(buf.as_mut_ptr()) };
    unsafe {
        let nn1 = nn.add(1);
        let nn3 = nn.add(3);
        let diff = nn3.offset_from(nn1);
        assert(diff == 2);
    }
}

// negative distance: nn1 is ahead, so nn1.offset_from(nn3) == -2
pub fn test_offset_from_neg(buf: &mut [i32; 4]) {
    let nn = unsafe { NonNull::new_unchecked(buf.as_mut_ptr()) };
    unsafe {
        let nn3 = nn.add(3);
        let nn1 = nn.add(1);
        let diff = nn1.offset_from(nn3);
        assert(diff == -2);
    }
}

// self offset_from self == 0
pub fn test_offset_from_zero(buf: &mut [i32; 4]) {
    let nn = unsafe { NonNull::new_unchecked(buf.as_mut_ptr()) };
    unsafe {
        let nn2 = nn.add(2);
        let diff = nn2.offset_from(nn2);
        assert(diff == 0);
    }
}

// --- offset_from_unsigned ---

// forward distance: same arithmetic as offset_from for self >= origin
pub fn test_offset_from_unsigned_pos(buf: &mut [i32; 4]) {
    let nn = unsafe { NonNull::new_unchecked(buf.as_mut_ptr()) };
    unsafe {
        let nn1 = nn.add(1);
        let nn3 = nn.add(3);
        let diff = nn3.offset_from_unsigned(nn1);
        assert(diff == 2);
    }
}

// self == origin: distance is zero
pub fn test_offset_from_unsigned_zero(buf: &mut [i32; 4]) {
    let nn = unsafe { NonNull::new_unchecked(buf.as_mut_ptr()) };
    unsafe {
        let nn2 = nn.add(2);
        let diff = nn2.offset_from_unsigned(nn2);
        assert(diff == 0);
    }
}

// roundtrip: nn.add(2).offset_from_unsigned(nn) == 2
pub fn test_offset_from_unsigned_roundtrip(buf: &mut [i32; 4]) {
    let nn = unsafe { NonNull::new_unchecked(buf.as_mut_ptr()) };
    unsafe {
        let nn2 = nn.add(2);
        assert(nn2.offset_from_unsigned(nn) == 2);
    }
}

// --- slice_from_raw_parts ---

// all 4 elements: requires satisfied (4 * 4 == 16 bytes fits in buf)
pub fn test_slice_from_raw_parts(buf: &mut [i32; 4]) {
    let nn = unsafe { NonNull::new_unchecked(buf.as_mut_ptr()) };
    let _slice_nn = NonNull::slice_from_raw_parts(nn, 4);
}

// partial slice: 2 elements (8 bytes) fits in the 16-byte buffer
pub fn test_slice_from_raw_parts_partial(buf: &mut [i32; 4]) {
    let nn = unsafe { NonNull::new_unchecked(buf.as_mut_ptr()) };
    let _slice_nn = NonNull::slice_from_raw_parts(nn, 2);
}
