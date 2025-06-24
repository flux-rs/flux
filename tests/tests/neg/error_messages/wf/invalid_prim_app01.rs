use flux_rs::{assert, attrs::*, defs};

defs! {
    property ShiftByTwo[<<](x, y) {
       y == 2 => [<<](x, y) == 4*x
    }

    property BadProp3Args[<<](x, y, z) {
       y + z == 2 => [<<](x, y) == 4*x
    }

    property BadProp3Args[<<]() {
       true
    }

    property BadPropWrongIn[<<](x, y) {
       y => [<<](x, y) == 4*x
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
