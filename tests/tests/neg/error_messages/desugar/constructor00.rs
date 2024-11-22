#[flux::refined_by(x: int, y: int)]
pub struct S {
    #[flux::field(u32[x])]
    x: u32,
    #[flux::field(u32[y])]
    y: u32,
}

impl S {
    // multiple spreads in constructor
    #[flux::sig(fn (self: &strg S[@old_x]) ensures self: S[S { x: 1, ..old_x, ..old_x }])] //~ERROR multiple spreads found in constructor
    pub fn foo(&mut self) {
        self.x = 1;
        self.y = 1;
    }
}
