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

// --- offset_from ---

// different allocations: p.base != q.base violates the same-allocation requirement.
// Alignment is constrained so that only the base check fails.
#[flux::spec(fn (p: {*const[@bp, @ap, @sp] i32 | ap >= bp && sp >= 0},
                  q: {*const[@bq, @aq, @sq] i32 | aq >= bq && sq >= 0 && bq != bp && (ap - aq) % 4 == 0}))]
pub fn test_offset_from_diff_base(p: *const i32, q: *const i32) {
    unsafe {
        let _ = p.offset_from(q); //~ ERROR refinement type error
    }
}

// non-element-aligned distance: q is 1 byte ahead of p, but T = i32 requires a multiple of 4
#[flux::spec(fn (p: {*const[@bp, @ap, @sp] i32 | ap >= bp && sp >= 0},
                  q: {*const[@bq, @aq, @sq] i32 | bq == bp && aq == ap + 1 && sq >= 0}))]
pub fn test_offset_from_unaligned(p: *const i32, q: *const i32) {
    unsafe {
        let _ = q.offset_from(p); //~ ERROR refinement type error
    }
}

// ZST: size_of::<()>() == 0, violating T::size_of() > 0. Other preconditions are all satisfied
// (same base, same address, so the distance is 0, which is a multiple of anything).
#[flux::spec(fn (p: {*const[@bp, @ap, @sp] () | ap >= bp && sp >= 0},
                  q: {*const[@bq, @aq, @sq] () | bq == bp && aq == ap && sq == sp}))]
pub fn test_offset_from_zst(p: *const (), q: *const ()) {
    unsafe {
        let _ = p.offset_from(q); //~ ERROR refinement type error
    }
}

// --- offset_from_unsigned ---

// origin is ahead of self: violates p.addr >= op.addr (all other preconditions are satisfied).
// aq = ap + 4 ensures (ap - aq) % 4 = (-4) % 4 = 0 in SMT-lib.
#[flux::spec(fn (p: {*const[@bp, @ap, @sp] i32 | ap >= bp && sp >= 0},
                  q: {*const[@bq, @aq, @sq] i32 | bq == bp && aq == ap + 4 && sq >= 0}))]
pub fn test_offset_from_unsigned_reversed(p: *const i32, q: *const i32) {
    unsafe {
        let _ = p.offset_from_unsigned(q); //~ ERROR refinement type error
    }
}

// --- cast ---

#[flux::spec(fn (ptr: {*mut[@base, @addr, @size] u8 | addr >= base && addr > 0 && size == 1 && addr % 8 == 0}))]
pub fn test_cast_method_does_not_create_extent(ptr: *mut u8) {
    let wide = ptr.cast::<u64>();
    unsafe {
        std::ptr::write(wide, 0); //~ ERROR refinement type error
    }
}

#[flux::spec(fn (ptr: {*mut[@base, @addr, @size] u8 | addr >= base && addr > 0 && size >= 8 && addr % 8 != 0}))]
pub fn test_cast_method_does_not_create_alignment(ptr: *mut u8) {
    let wide = ptr.cast::<u64>();
    unsafe {
        std::ptr::write(wide, 0); //~ ERROR refinement type error
    }
}

#[flux::spec(fn (ptr: {*mut[@base, @addr, @size] i32 | addr >= base && addr > 0 && size < 4 && addr % 4 == 0}))]
pub fn test_cast_const_method_preserves_extent(ptr: *mut i32) {
    let const_ptr = ptr.cast_const();
    unsafe {
        let _value = std::ptr::read(const_ptr); //~ ERROR refinement type error
    }
}

#[flux::spec(fn (ptr: {*const[@base, @addr, @size] i32 | addr >= base && addr > 0 && size < 4 && addr % 4 == 0}))]
pub fn test_cast_mut_method_preserves_extent(ptr: *const i32) {
    let mut_ptr = ptr.cast_mut();
    unsafe {
        std::ptr::write(mut_ptr, 0); //~ ERROR refinement type error
    }
}
