#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(n: int)]
pub enum List<T> {
    #[flux::variant(Self[0])]
    Nil,
    #[flux::variant((T, Box<Self[@n]>) -> Self[n+1])]
    Cons(T, Box<Self>),
}
