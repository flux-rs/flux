use flux_rs::{assert, defs};

defs! {
    property shift_by_two[<<](x:int, y:int) -> int {
        y == 2 => [<<](x, y) == 4*x
    }
}

pub fn test() {
    let x: usize = 1 << 2;
    assert(x == 4);
    // let x = 1;
    // let x = x << 2;
    // let x = x << 2;
    // assert(x == 16)
}
