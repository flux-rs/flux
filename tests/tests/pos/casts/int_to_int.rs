use flux_rs::attrs::*;

#[spec(fn() -> i32[1])]
pub fn bool_int() -> i32 {
    true as i32
}

#[spec(fn() -> u32[0])]
pub fn bool_uint() -> u32 {
    false as u32
}

#[spec(fn() -> u32[42])]
pub fn uint_uint_lossless() -> u32 {
    42u8 as u32
}

#[spec(fn() -> i32[42])]
pub fn int_int_lossless() -> i32 {
    42i8 as i32
}

#[spec(fn() -> i32[42])]
pub fn uint_int_lossless() -> i32 {
    42u8 as i32
}

#[spec(fn() -> usize[42])]
pub fn unsigned_to_usize() -> usize {
    42u32 as usize
}

#[spec(fn(n:u64{n < 100}) -> u32{v: v < 100})]
pub fn uint_uint_lossy(n: u64) -> u32 {
    n as u32
}

#[spec(fn(n:u32{n < 100}) -> u64{v: v < 100})]
pub fn uint_uint_lossless2(n: u32) -> u64 {
    n as u64
}

const ROOT_NANOS_PER_SEC: u32 = 1_000_000_000;

#[spec(fn(nanos:u64) -> u64{v: 0 <= v && v < ROOT_NANOS_PER_SEC})]
pub fn test64(nanos: u64) -> u64 {
    const NANOS_PER_SEC: u64 = ROOT_NANOS_PER_SEC as u64;
    let subsec_nanos = nanos % NANOS_PER_SEC;
    subsec_nanos
}

#[spec(fn(nanos:u64) -> u32{v: 0 <= v && v < ROOT_NANOS_PER_SEC})]
pub fn test32(nanos: u64) -> u32 {
    const NANOS_PER_SEC: u64 = ROOT_NANOS_PER_SEC as u64;
    let subsec_nanos = (nanos % NANOS_PER_SEC) as u32;
    subsec_nanos
}
