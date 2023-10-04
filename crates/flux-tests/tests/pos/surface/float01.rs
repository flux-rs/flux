#[flux::sig(fn(f32) -> f32)]
pub fn float01(x: f32) -> f32 {
    let y = x + 0.1;
    if x > 0.0 {
        -x + 0.3
    } else if x == 0.0 {
        x + y
    } else {
        x
    }
}
