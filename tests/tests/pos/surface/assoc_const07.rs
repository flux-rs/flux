// From nilehmann's `assoc_const_reflected` example on PR #1733.
//
// An associated constant whose value is a variant of a reflected enum. Const evaluation only
// handles scalar types, so the value comes from the `#[constant(State::On)]` annotation.

use flux_attrs::*;

#[reflect]
pub enum State {
    On,
    Off,
}

pub trait Machine {
    const INIT: State;

    #[spec(fn() -> State[Self::INIT])]
    fn start() -> State;
}

pub struct Simple;

impl Machine for Simple {
    #[constant(State::On)]
    const INIT: State = State::On;

    #[spec(fn() -> State[Self::INIT])]
    fn start() -> State {
        State::On
    }
}

#[spec(fn() -> State[State::On])]
pub fn test() -> State {
    <Simple as Machine>::start()
}
