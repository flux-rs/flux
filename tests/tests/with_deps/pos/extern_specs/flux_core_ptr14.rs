extern crate flux_core;

// Without wrapping, the wrapping operations are ordinary pointer arithmetic.
#[flux::spec(fn(ptr: *const[@p] u8, n: usize) -> *const{q: q.base == p.base && q.addr == p.addr - n && q.size == p.size + n} u8
    requires n <= p.addr)]
pub fn test_wrapping_sub(ptr: *const u8, n: usize) -> *const u8 {
    ptr.wrapping_sub(n)
}

#[flux::spec(fn(ptr: *mut[@p] i32, n: usize) -> *mut{q: q.base == p.base && q.addr == p.addr + 4 * n && q.size == p.size - 4 * n} i32
    requires p.addr + 4 * n <= usize::MAX)]
pub fn test_wrapping_add(ptr: *mut i32, n: usize) -> *mut i32 {
    ptr.wrapping_add(n)
}

#[flux::spec(fn(ptr: *const[@p] i32) -> *const{q: q.base == p.base && q.addr == p.addr - 8} i32
    requires p.addr >= 8)]
pub fn test_wrapping_offset(ptr: *const i32) -> *const i32 {
    ptr.wrapping_offset(-2)
}

#[flux::spec(fn(ptr: *const[@p] i32) -> *const{q: q.addr == p.addr - 3} i32
    requires p.addr >= 3)]
pub fn test_wrapping_byte_offset(ptr: *const i32) -> *const i32 {
    ptr.wrapping_byte_offset(-3)
}

// Subtracting more than the address wraps around to the top of the address space.
#[flux::spec(fn(ptr: *const[@p] u8) -> *const{q: q.addr == p.addr - 16 + usize::MAX + 1} u8
    requires p.addr < 16)]
pub fn test_wrapping_sub_wraps(ptr: *const u8) -> *const u8 {
    ptr.wrapping_byte_sub(16)
}

// Round trips are exact, and keep the allocation.
#[flux::spec(fn(ptr: *mut[@p] u8, n: usize) -> *mut[p.base, p.addr, p.size] u8)]
pub fn test_round_trip(ptr: *mut u8, n: usize) -> *mut u8 {
    ptr.wrapping_add(n).wrapping_sub(n)
}

// `size` keeps counting up to the end of the allocation, even past it.
#[flux::spec(fn(ptr: *const[@p] u64, n: usize) -> *const{q: q.addr + q.size == p.addr + p.size} u64)]
pub fn test_end_preserved(ptr: *const u64, n: usize) -> *const u64 {
    ptr.wrapping_add(n)
}

// Adding `usize::MAX` bytes is equivalent to subtracting one modulo the
// address-space size.
#[flux::spec(fn(ptr: *const[@p] u8) -> *const{q: q.addr == p.addr - 1} u8 requires p.addr >= 1)]
pub fn test_wrapping_add_max(ptr: *const u8) -> *const u8 {
    ptr.wrapping_byte_add(usize::MAX)
}

// `count * size_of::<T>()` may overflow; the address is still exact.
#[flux::spec(fn(ptr: *const[@p] u64) -> *const{q: q.addr == p.addr - 8} u64 requires p.addr >= 8)]
pub fn test_wrapping_add_overflowing_count(ptr: *const u64) -> *const u64 {
    ptr.wrapping_add(usize::MAX)
}

// Adding past the top of the address space wraps around to the bottom.
#[flux::spec(fn(ptr: *const[@p] u8) -> *const{q: q.addr == p.addr + 16 - (usize::MAX + 1)} u8
    requires p.addr > usize::MAX - 16)]
pub fn test_wrapping_add_wraps(ptr: *const u8) -> *const u8 {
    ptr.wrapping_byte_add(16)
}

// Element-based wrapping on a ZST leaves the pointer unchanged for any count.
#[flux::spec(fn(ptr: *const[@p] (), n: usize, k: usize, m: isize) -> *const[p.base, p.addr, p.size] ())]
pub fn test_wrapping_zst(ptr: *const (), n: usize, k: usize, m: isize) -> *const () {
    ptr.wrapping_add(n).wrapping_sub(k).wrapping_offset(m)
}

// `isize::MIN` bytes is half the address space, so it flips the top bit of the address.
#[flux::spec(fn(ptr: *const[@p] u8) -> *const{q: q.addr == p.addr + isize::MAX + 1} u8
    requires p.addr <= isize::MAX)]
pub fn test_wrapping_byte_offset_min_low(ptr: *const u8) -> *const u8 {
    ptr.wrapping_byte_offset(isize::MIN)
}

#[flux::spec(fn(ptr: *const[@p] u8) -> *const{q: q.addr == p.addr + isize::MIN} u8
    requires isize::MAX < p.addr)]
pub fn test_wrapping_byte_offset_min_high(ptr: *const u8) -> *const u8 {
    ptr.wrapping_byte_offset(isize::MIN)
}

#[flux::spec(fn(ptr: *const[@p] u8) -> *const{q: q.addr == p.addr + isize::MAX + 1} u8
    requires p.addr <= isize::MAX)]
pub fn test_wrapping_offset_min(ptr: *const u8) -> *const u8 {
    ptr.wrapping_offset(isize::MIN)
}

// `isize::MIN * 8` is a multiple of the address-space size, so the address is unchanged.
#[flux::spec(fn(ptr: *const[@p] u64) -> *const{q: q.addr == p.addr} u64)]
pub fn test_wrapping_offset_min_scaled(ptr: *const u64) -> *const u64 {
    ptr.wrapping_offset(isize::MIN)
}
