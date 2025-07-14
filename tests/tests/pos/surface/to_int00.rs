#![flux::defs {
    fn as_int(x:int) -> int {
        x
    }

    fn is_ascii_digit(c:char) -> bool {
        let i = cast(c);
        as_int(48) <= i && i <= as_int(57)
    }

    fn is_ascii(c:char) -> bool {
        let i = cast(c);
        as_int(0) <= i && i <= as_int(127)
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

pub fn test_ok(x: char) {
    if x.is_ascii_digit() {
        assert(x.is_ascii())
    }
}

#[spec(fn (char{v: '0' <= v && v <= '9'}))]
pub fn test_digit(x: char) {
    assert(x.is_ascii_digit())
}
