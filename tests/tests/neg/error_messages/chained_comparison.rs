#[flux::sig(fn(x: i32, y: i32, z: i32) -> bool[x < y < z])] //~ ERROR syntax error
pub fn chained_comparison(x: i32, y: i32, z: i32) -> bool {
    x < y && y < z
}
