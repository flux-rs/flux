use flux_rs::*;

const FORTY_TWO: usize = 21 + 21;

#[spec(fn() -> bool[false])]
pub fn test00() -> bool {
    FORTY_TWO == 40 + 2 //~ ERROR refinement type
}

trait Trait {
    const C: usize;
}

fn test01<T: Trait>() -> usize {
    T::C
}

#[spec(fn() -> usize[0])]
fn test02() -> usize {
    const { 0 + 1 } //~ ERROR refinement type
}
