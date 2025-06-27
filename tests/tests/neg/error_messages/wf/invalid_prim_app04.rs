use flux_rs::{assert, defs};

defs! {
    property BadPropWrongOp[+](x, y) { //~ ERROR properties for `+` are not yet supported
       x + y == 0 => [+](x, y) == 0
    }
}

pub fn test0() {
    let x: usize = 1 << 2;
    assert(x == 4);
}
