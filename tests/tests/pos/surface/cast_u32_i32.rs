#[flux::sig(fn(fp: u32{fp <= i32::MAX}) -> i32[fp])]
pub fn u32_to_i32(fp: u32) -> i32 {
    fp as i32
}
