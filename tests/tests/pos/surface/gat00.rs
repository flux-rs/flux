// Test that generic associated types with lifetime parameters work correctly.
// See issue #1716.

pub trait D {
    type Tok<'a>;
}

pub struct L;

impl D for L {
    type Tok<'a> = &'a L;
}

pub fn f(x: &L) -> <L as D>::Tok<'_> {
    x
}
