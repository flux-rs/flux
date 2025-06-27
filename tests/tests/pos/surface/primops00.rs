use flux_rs::{assert, attrs::*, defs};

defs! {
    property ShiftByTwo[<<](x, y) {
       [<<](x, 2) == 4*x
    }

    property ShiftRightByFour[>>](x, y) {
       16 * [>>](x, 4) == x
    }

    property MaskBy15[&](x, y) {
        [&](x, y) <= y
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
