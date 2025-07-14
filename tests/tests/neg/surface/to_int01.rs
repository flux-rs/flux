use flux_rs::attrs::*;

#[spec(fn (x:bool) -> u32[to_int(x)])]
pub fn test_bool_to_int(_x: bool) -> u32 {
    0 //~ ERROR refinement type
}

#[spec(fn (x:bool) -> u32[to_int(x)])]
pub fn test_bool_to_int_with_if(x: bool) -> u32 {
    if x { 1 } else { 1 } //~ERROR refinement type
}
