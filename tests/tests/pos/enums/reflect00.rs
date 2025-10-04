use flux_rs::attrs::*;

#[reflect]
pub enum State {
    On,
    Off,
}

#[spec(fn () -> State[State::On])]
pub fn test00() -> State {
    State::On
}

#[spec(fn () -> State[State::Off])]
pub fn test01() -> State {
    State::Off
}
