use flux_attrs::*;

#[flux::spec(fn(ptr: *const[@p] u8) -> usize[p.addr])]
pub fn const_ptr_to_usize(p: *const u8) -> usize {
    p as usize
}

#[flux::spec(fn(ptr: *mut[@p] u8) -> usize[p.addr])]
pub fn mut_ptr_to_usize(p: *mut u8) -> usize {
    p as usize
}

#[flux::spec(fn(ptr: *const[@p] u8) -> u64[p.addr])]
pub fn const_ptr_to_u64(p: *const u8) -> u64 {
    p as u64
}

#[flux::spec(fn(ptr: *const[@p] u8) -> i128[p.addr])]
pub fn const_ptr_to_i128(p: *const u8) -> i128 {
    p as i128
}

#[flux::spec(fn(ptr: *const[@p] u8) -> u8[p.addr]
    requires 0 <= p.addr && p.addr <= 255)]
pub fn const_ptr_to_u8_if_addr_fits(p: *const u8) -> u8 {
    p as u8
}

#[flux::spec(fn(ptr: {*const[@p] u8 | p.addr == 0}) -> usize[0])]
pub fn null_ptr_to_usize(p: *const u8) -> usize {
    p as usize
}
