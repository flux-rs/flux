#[flux::refined_by(n:int)]
#[flux::invariant(n > 0)] //~ ERROR invariant
pub enum List<T> {
    #[flux::variant(List<T>[0])]
    Nil,
    #[flux::variant({T, Box<List<T>[@n]>} -> List<T>[n+1])]
    Cons(T, Box<List<T>>),
}

#[flux::refined_by(n: int)]
#[flux::invariant(n > 1)] //~ ERROR invariant
pub enum Pos {
    #[flux::variant({Box<Pos[@n]>} -> Pos[2*n])]
    XO(Box<Pos>),
    #[flux::variant({Box<Pos[@n]>} -> Pos[2*n + 1])]
    XI(Box<Pos>),
    #[flux::variant(Pos[1])]
    XH,
}
