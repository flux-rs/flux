// Test use of constant in fn-signature
use flux_rs::*;

pub const FORTY_TWO: usize = 21 + 21;

#[spec(fn() -> usize{v: v < FORTY_TWO})]
pub fn test01() -> usize {
    13 + 50 //~ ERROR refinement type
}
