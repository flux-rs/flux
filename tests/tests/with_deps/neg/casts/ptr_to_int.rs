use flux_attrs::*;

#[flux::spec(fn(ptr: *const[@p] u8) -> usize[p.addr + 1])]
pub fn wrong_addr(p: *const u8) -> usize {
    p as usize //~ ERROR refinement type
}

#[flux::spec(fn(ptr: *const[@p] u8) -> u8[p.addr])]
pub fn narrowing_without_bound(p: *const u8) -> u8 {
    p as u8 //~ ERROR refinement type
}

#[flux::spec(fn(ptr: *const[@p] u8) -> isize[p.addr])]
pub fn potentially_lossy_signed_cast(p: *const u8) -> isize {
    p as isize //~ ERROR refinement type
}
