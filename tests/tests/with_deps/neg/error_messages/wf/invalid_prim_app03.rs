use flux_rs::{assert, defs};

defs! {
    property BadPropWrongOut[<<](x, y) {
       x + y == 2 => [<<](x, y) //~ ERROR mismatched sorts
    }
}

pub fn test0() {
    let x: usize = 1 << 2;
    assert(x == 4);
}
