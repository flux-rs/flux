// Negative version of pos/surface/assoc_const07.rs: `Simple::INIT` is `State::On`, not `State::Off`.

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
        State::Off //~ ERROR refinement type
    }
}

#[spec(fn() -> State[State::Off])]
pub fn test() -> State {
    <Simple as Machine>::start() //~ ERROR refinement type
}
