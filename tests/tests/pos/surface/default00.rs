// No signature -- test that we can just create a trivial "unrefined" signature for `silly`.
fn silly(x: i32) -> i32 {
    x
}

#[flux::sig(fn(x: i32) -> i32{v : x < v})]
pub fn inc(x: i32) -> i32 {
    let y = silly(x);
    if x < y {
        y
    } else {
        x + 1
    }
}
