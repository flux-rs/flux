use flux_rs::{assert, defs};

defs! {
    property ShiftByTwo[<<](x:int, y:int) { //~ ERROR syntax error
       [<<](x, 2) == 4*x
    }
}

pub fn test0() {
    let x: usize = 1 << 2;
    assert(x == 4);
}
