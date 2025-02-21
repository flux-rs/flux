#[flux::reflect]
pub enum State {
    #[flux::variant(State[0])]
    On, //~ ERROR reflected types cannot have refinement annotations
    #[flux::variant(State[1])]
    Off, //~ ERROR reflected types cannot have refinement annotations
}
