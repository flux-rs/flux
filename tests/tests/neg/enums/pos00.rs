#[flux::refined_by(n: int)]
pub enum Pos {
    #[flux::variant({Box<Pos[@n]>} -> Pos[2*n])]
    XO(Box<Pos>),
    #[flux::variant({Box<Pos[@n]>} -> Pos[2*n + 1])]
    XI(Box<Pos>),
    #[flux::variant(Pos[1])]
    XH,
}

impl Pos {
    #[flux::sig(fn(&Pos[@n]) -> i32[n])]
    pub fn to_i32(&self) -> i32 {
        match self {
            Pos::XH => 1,
            Pos::XI(rest) => 2 * rest.to_i32(), //~ ERROR refinement type
            Pos::XO(rest) => 2 * rest.to_i32(),
        }
    }

    #[flux::sig(fn(&Pos[@n]) -> bool[n == 1])]
    pub fn is_one(&self) -> bool {
        match self {
            Pos::XH => true,
            Pos::XI(_) => false, //~ ERROR refinement type
            Pos::XO(_) => false,
        }
    }
}
