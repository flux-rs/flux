use flux_rs::{assert, defs};

defs! {
    property[<<] fn shift_by_two(x:int, y:int) {
        y == 2 => [<<](x, y) == 4*x
    }
}

pub fn test() {
    let x = 1;
    let x = x << 2;
    let x = x << 2;
    assert(x == 16)
}
