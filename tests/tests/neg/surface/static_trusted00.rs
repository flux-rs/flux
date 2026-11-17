//! Without `trusted` the initializer is checked.

#[flux::spec(u32[1])]
static ONE: u32 = 2; //~ ERROR refinement type
