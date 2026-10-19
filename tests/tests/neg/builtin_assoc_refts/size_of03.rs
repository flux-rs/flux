use flux_attrs::*;

pub struct Foo {
    _x: i64,
}

defs! {
    fn foo_size() -> int {
        <Foo as Sized>::size_of()
    }
}

#[spec(fn() -> usize[foo_size()])]
pub fn test() -> usize {
    4 //~ ERROR refinement type
}
