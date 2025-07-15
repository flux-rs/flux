#![flux::defs {
    // wrapper to monomorphize cast
    fn cast_to_int(x:char) -> int {
        cast(x)
    }

    fn is_ascii_digit(c:char) -> bool {
        let i = cast_to_int(c);
        48 <= i && i <= 57
    }

    fn is_ascii(c:char) -> bool {
        let i = cast_to_int(c);
        0 <= i && i <= 127
    }
}]

use flux_rs::{assert, attrs::*};

// extern specs for is_ascii and is_ascii_digit
#[extern_spec]
impl char {
    #[spec(fn (&Self[@c]) -> bool[is_ascii(c)])]
    fn is_ascii(&self) -> bool;

    #[spec(fn (&Self[@c]) -> bool[is_ascii_digit(c)])]
    fn is_ascii_digit(&self) -> bool;
}

pub fn test_err(x: char) {
    if x.is_ascii() {
        assert(x.is_ascii_digit()) //~ ERROR refinement type
    }
}
