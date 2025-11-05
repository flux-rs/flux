use flux_rs::{assert, attrs::*, defs};

defs! {

    fn is_char(n: int) -> bool {
        0 <= n && n <= 0x10FFFF
    }

    property ShiftByTwo[<<](x, y) {
        [<<](x, 2) == 4*x
    }

    property ShiftRightByFour[>>](x, y) {
        16 * [>>](x, 4) == x
    }

    property MaskBy[&](x, y) {
        [&](x, y) <= y
    }

    property XorSelfInverse[^](x, y) {
        x == y => [^](x, y) == 0
    }

    property OrBy1[|](x, y) {
        is_char(x) => is_char([|](x, 1))
    }
}

pub fn test0() {
    let x: usize = 1 << 2;
    assert(x == 4);
}

pub fn test1() {
    let x = 1;
    let x = x << 2;
    let x = x << 2;
    assert(x == 16)
}

#[spec(fn (x: u32) -> u32[16*x])]
pub fn test2(x: u32) -> u32 {
    let x = x << 2;
    let x = x << 2;
    x
}

#[spec(fn (byte: u8{byte <= 127}))]
pub fn test3(byte: u8) {
    let tmp1 = byte >> 4;
    let tmp2 = byte & 0xf;
    assert(byte <= 127);
    assert(tmp1 <= 0xf);
    assert(tmp2 <= 0xf);
}

static POW10: [i32; 10] = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

pub fn test4(n: usize) -> i32 {
    POW10[n & 7]
}

#[spec(fn(x: usize) -> usize[0])]
pub fn test5(x: usize) -> usize {
    x ^ x
}

pub fn test6(c: char) {
    let c = c as u32;
    flux_rs::assert(c <= 0x10FFFF); // (0)
    let c = c | 1;
    flux_rs::assert(c <= 0x10FFFF); // (1)
}
