use flux_rs::{assert, defs};

defs! {
    property ShiftByTwo[<<](x:int, y:int) -> int {
       y == 2 => [<<](x, y) == 4*x
    }
}

pub fn test2() {
    let x = 1;
    let x = x << 2;
    let x = x << 2;
    assert(x == 15) //~ ERROR refinement type error
}
