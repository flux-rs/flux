use flux_rs::{assert, defs};

defs! {
    property BadProp3Args[<<]() { //~ ERROR this primop takes 2
       true
    }

    property BadPropWrongOut[<<](x, y) {
       x + y == 2 => [<<](x, y)
    }

    property BadPropWrongOp[+](x, y) {
       x + y == 0 => [+](x, y) == 0
    }
}

pub fn test0() {
    let x: usize = 1 << 2;
    assert(x == 4);
}
