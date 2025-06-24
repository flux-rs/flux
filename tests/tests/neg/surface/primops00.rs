use flux_rs::{assert, defs};

defs! {
    property [<<] fn shift_by_two(x:int, y:int) {
        y == 2 => [<<](x, y) == 4*x
    }
}

// TODO FIX SYNTAX to include output sort
//    property shift_by_two[<<](x:int, y:int) -> int {
//        y == 2 => [<<](x, y) == 4*x
//    }

pub fn test0() {
    let x: usize = 1 << 2;
    assert(x == 4);
}

pub fn test1() {
    let x = 1;
    let x = x << 2;
    let x = x << 2;
    assert(x == 16)
}

pub fn test2() {
    let x = 1;
    let x = x << 2;
    let x = x << 2;
    assert(x == 15) //~ ERROR refinement type error
}
