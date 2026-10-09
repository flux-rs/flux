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

#[flux::reflect]
pub enum TupleState {
    A(),
}

use TupleState::A;

#[flux::spec(fn() -> TupleState[A])]
pub fn tuple_unqualified() -> TupleState {
    A()
}

#[flux::spec(fn() -> TupleState[TupleState::A])]
pub fn tuple_qualified() -> TupleState {
    TupleState::A()
}
