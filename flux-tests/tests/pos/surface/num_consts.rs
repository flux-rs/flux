#![feature(register_tool)]
#![register_tool(flux)]

#[flux::sig(fn() -> (i8[i8::MIN], i8[i8::MAX]))]
fn test_i8() -> (i8, i8) {
    (i8::MIN, i8::MAX)
}

#[flux::sig(fn() -> (i16[i16::MIN], i16[i16::MAX]))]
fn test_i16() -> (i16, i16) {
    (i16::MIN, i16::MAX)
}

#[flux::sig(fn() -> (i32[i32::MIN], i32[i32::MAX]))]
fn test_i32() -> (i32, i32) {
    (i32::MIN, i32::MAX)
}

#[flux::sig(fn() -> (i64[i64::MIN], i64[i64::MAX]))]
fn test_i64() -> (i64, i64) {
    (i64::MIN, i64::MAX)
}

#[flux::sig(fn() -> (isize[isize::MIN], isize[isize::MAX]))]
fn test_isize() -> (isize, isize) {
    (isize::MIN, isize::MAX)
}

#[flux::sig(fn() -> (u8[u8::MIN], u8[u8::MAX]))]
fn test_u8() -> (u8, u8) {
    (u8::MIN, u8::MAX)
}

#[flux::sig(fn() -> (u16[u16::MIN], u16[u16::MAX]))]
fn test_u16() -> (u16, u16) {
    (u16::MIN, u16::MAX)
}

#[flux::sig(fn() -> (u32[u32::MIN], u32[u32::MAX]))]
fn test_u32() -> (u32, u32) {
    (u32::MIN, u32::MAX)
}

#[flux::sig(fn() -> (u64[u64::MIN], u64[u64::MAX]))]
fn test_u64() -> (u64, u64) {
    (u64::MIN, u64::MAX)
}

#[flux::sig(fn() -> (usize[usize::MIN], usize[usize::MAX]))]
fn test_usize() -> (usize, usize) {
    (usize::MIN, usize::MAX)
}
