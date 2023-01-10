#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(b:bool)]
pub enum E1<T> {
    #[flux::variant(Opt<T>[false])] //~ ERROR cannot resolve
    A,
    #[flux::variant({T} -> Opt<T>[true])] //~ ERROR cannot resolve
    B(T),
}
