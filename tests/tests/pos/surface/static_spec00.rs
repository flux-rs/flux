#[flux::static_spec(u32[67])]
static BLAH: u32 = 67;

#[flux::sig(fn () -> u32[67])]
pub fn test_blah() -> u32 {
    BLAH
}

#[flux::static_spec([u32[67]; 3])]
static FROG: [u32; 3] = [67, 67, 67];

#[flux::sig(fn () -> u32[67])]
pub fn test_frog() -> u32 {
    FROG[0]
}

#[flux::static_spec([u32{v:v < 100}; 3])]
static HOG: [u32; 3] = [67, 67, 67];

#[flux::sig(fn () -> u32{v:v < 300})]
pub fn test_hog() -> u32 {
    HOG[0] + HOG[1] + HOG[2]
}
