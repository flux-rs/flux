// #[flux::static_spec(u32[67])]
// static BLAH: u32 = 67;

// #[flux::sig(fn () -> u32[67])]
// pub fn test_blah() -> u32 {
//     BLAH
// }

#[flux::static_spec([u32[67]; 3])]
static FROG: [u32; 3] = [67, 67, 67];

#[flux::sig(fn () -> u32[67])]
pub fn test_frog() -> u32 {
    FROG[0]
}
