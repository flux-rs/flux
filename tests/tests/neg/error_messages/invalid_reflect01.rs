#[flux::reflect]
pub enum State {
    #[flux::variant(State[0])]
    On, //~ ERROR invalid variant for reflected enum
    #[flux::variant(State[1])]
    Off, //~ ERROR invalid variant for reflected enum
}


