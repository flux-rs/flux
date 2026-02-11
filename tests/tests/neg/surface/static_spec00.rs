static BLAH: u32 = 67;

#[flux::sig(fn () -> u32[67])]
pub fn test_blah() -> u32 {
    BLAH //~ ERROR refinement type
}

static FROG: [u32; 3] = [67, 67, 67];

#[flux::sig(fn () -> u32[67])]
pub fn test_frog() -> u32 {
    FROG[0] //~ ERROR refinement type
}

static HOG: [u32; 3] = [67, 67, 67];

#[flux::sig(fn () -> u32{v:v < 300})]
pub fn test_hog() -> u32 {
    HOG[0] + HOG[1] + HOG[2] //~ ERROR refinement type
}
