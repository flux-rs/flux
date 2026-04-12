use flux_attrs::*;

const FORTY_TWO: usize = 21 + 21;

#[spec(fn() -> bool[true])]
pub fn test00() -> bool {
    FORTY_TWO == 40 + 2
}

trait Trait {
    const C: usize;
}

fn test01<T: Trait>() -> usize {
    T::C
}

#[spec(fn() -> usize[1])]
fn test02() -> usize {
    const { 0 + 1 }
}
