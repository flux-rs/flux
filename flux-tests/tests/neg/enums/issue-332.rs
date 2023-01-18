#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(n: int)]
pub enum List {
    #[flux::variant(List[0])]
    Nil,
    #[flux::variant((Box<List[@n]>) -> List[n+1])]
    Cons(Box<List>),
}

impl List {
    #[flux::sig(
        fn(self: &strg List[@n1], List[@n2])
        ensures self: List[n1 + n2]
    )]
    pub fn append(&mut self, other: List) {
        if let List::Cons(tl) = self {
            tl.append(other)
        }
    } //~ ERROR postcondition
}
