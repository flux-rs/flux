// #[flux_rs::reflect]
pub enum State {
    On,
    Off,
}

#[flux_rs::sig(fn () -> State[On])]
pub fn test00() -> State {
    State::On
}

#[flux_rs::sig(fn () -> State[Off])]
pub fn test01() -> State {
    State::Off
}
