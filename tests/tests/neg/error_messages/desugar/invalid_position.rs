use flux_attrs::*;

pub struct Foo;

defs! {
    fn test00() -> int {
        1(0) //~ ERROR expression not allowed in this position
    }

    fn test01() -> int {
        <Foo as Sized>::size_of + 1 //~ ERROR expression not allowed in this position
    }
}
