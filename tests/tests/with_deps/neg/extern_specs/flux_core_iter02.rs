extern crate flux_core;

#[flux_rs::spec(fn(target: &mut [i32][@len], xs: &[i32]{n: n <= len + 1}))]
pub fn test_cloned_loop_out_of_bounds(target: &mut [i32], xs: &[i32]) {
    let mut i = 0;
    for x in xs.iter().cloned() {
        target[i] = x; //~ ERROR assertion might fail
        i += 1;
    }
}

#[flux_rs::spec(fn(target: &mut [i32][@len], xs: &[i32]{n: n <= len + 1}))]
pub fn test_copied_loop_out_of_bounds(target: &mut [i32], xs: &[i32]) {
    let mut i = 0;
    for x in xs.iter().copied() {
        target[i] = x; //~ ERROR assertion might fail
        i += 1;
    }
}
