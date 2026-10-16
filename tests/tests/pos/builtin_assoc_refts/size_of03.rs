// Rust paths in the body of a flux function definition

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
    8
}

// A definition nested in a generic item can use paths that don't mention the item's generics
pub fn nested<T>() {
    defs! {
        fn i64_size() -> int {
            <i64 as Sized>::size_of()
        }
    }

    #[spec(fn() -> usize[i64_size()])]
    fn test() -> usize {
        8
    }
}
