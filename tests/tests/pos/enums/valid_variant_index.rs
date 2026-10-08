#[flux::reflect]
pub enum State {
    On,
    Off,
}

use State::On;

#[flux::spec(fn() -> State[On])]
pub fn unqualified() -> State {
    On
}

#[flux::spec(fn() -> State[State::Off])]
pub fn qualified() -> State {
    State::Off
}
