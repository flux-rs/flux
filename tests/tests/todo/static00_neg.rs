#[flux::static([u32{v: v < 3}; _])]
static XS: [u32; 5] = [1, 2, 3, 4, 5]; //~ ERROR refinement type

