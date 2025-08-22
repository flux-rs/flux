#[flux::reflect]
pub enum State {
    On,
    Off,
}

#[flux_rs::sig(fn () -> State[On])] //~ ERROR cannot find value `On`
pub fn test00() -> State {
    State::On
}
