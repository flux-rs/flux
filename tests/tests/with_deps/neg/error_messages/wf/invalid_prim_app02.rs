use flux_rs::{assert, defs};

defs! {

    property BadPropWrongIn[<<](x, y) {
       y => [<<](x, 2) == 4*x //~ ERROR mismatched sorts
    }

}

pub fn test0() {
    let x: usize = 1 << 2;
    assert(x == 4);
}
