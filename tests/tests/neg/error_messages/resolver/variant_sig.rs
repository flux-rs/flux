#[flux::refined_by(b:bool)]
pub enum E1<T> {
    #[flux::variant(Opt<T>[false])] //~ ERROR cannot resolve type `Opt` in this scope
    A,
    #[flux::variant({T} -> Opt<T>[true])] //~ ERROR cannot resolve type `Opt` in this scope
    B(T),
}
