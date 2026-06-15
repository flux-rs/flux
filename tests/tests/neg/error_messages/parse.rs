use flux_attrs::*;

#[flux::opaque]
struct S {
    #[flux::field(i32[0])] //~ ERROR opaque struct can't have refined fields
    f: i32,
}

#[flux::refined_by(x: int)]
enum E {
    A(i32), //~ ERROR missing variant
}

defs! {
    fn test00() -> bool {
        true <=> false <=> true //~ ERROR syntax error
    }
}

defs! {
    fn test01() -> bool {
        0 < 1 < 2 //~ ERROR syntax error
    }
}
