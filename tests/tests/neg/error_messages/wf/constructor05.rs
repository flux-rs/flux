#[flux::refined_by(x: int, y: int)]
pub struct S {
    #[flux::field(u32[x])]
    x: u32,
    #[flux::field(u32[y])]
    y: u32,
}

#[flux::refined_by(x: int, y: int)]
pub enum E {
    #[flux::variant(E[0, 1])]
    VariantOne,
    #[flux::variant(E[1, 2])]
    VariantTwo,
    #[flux::variant(E[2, 3])]
    VariantThree,
}

impl S {
    // The constructor's spread `..e` is wrong
    #[flux::sig(fn (self: &strg S[@old_x], E[@e]) ensures self: S[S { x: 1, ..e }])] //~ERROR mismatched sorts
    pub fn crazy(&mut self, _e: E) {
        self.x = 1;
        self.y = 1;
    }
}
