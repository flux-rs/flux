#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(b:bool)]
pub enum Opt<T> {
    #[flux::variant(Opt<T>[false])]
    None,
    #[flux::variant(Opt<T>[true])] //~ ERROR field count mismatch
    Some(T),
}
