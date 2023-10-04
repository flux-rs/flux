#[flux::sig(fn(f32) -> f32)]
pub fn float00(x: f32) -> f32 {
    let y = x + 0.1;
    x - y
}

#[flux::sig(fn(f32, f32) -> bool)]
pub fn float01(x: f32, y: f32) -> bool {
    x == y
}
