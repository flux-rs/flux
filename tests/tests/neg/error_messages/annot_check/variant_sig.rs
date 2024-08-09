#[flux::refined_by(b:bool)]
pub enum Opt<T> {
    #[flux::variant(Opt<T>[false])]
    None,
    #[flux::variant(Opt<T>[true])] //~ ERROR incompatible refinement
    Some(T),
}
