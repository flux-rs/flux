#[flux::refined_by(x: int, y: int)]
pub struct S {
    #[flux::field(u32[x])]
    x: u32,
    #[flux::field(u32[y])]
    y: u32,
}

impl S {
    #[flux::sig(fn (self: &strg S[@old_x]) ensures self: S[S { x: 1, ..old_x }])]
    pub fn update(&mut self) {
        self.x = 1;
    }
}
