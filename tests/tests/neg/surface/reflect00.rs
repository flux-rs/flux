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

#[spec(fn () -> State[State::Off])]
pub fn test02() -> State {
    State::On //~ ERROR refinement type
}

#[spec(fn (State[State::On]) -> usize[1])]
pub fn test03(s: State) -> usize {
    match s {
        State::On => 1,
        State::Off => 0,
    }
}

#[spec(fn (State[@squig], zig: usize, tag: Day) -> usize[tag])]
pub fn test04(s: State, _zig: usize, tag: Day) -> usize {
    match s {
        State::On => 1,  //~ ERROR refinement type
        State::Off => 0, //~ ERROR refinement type
    }
}

#[refined_by(day: int)]
pub enum Day {
    #[flux::variant(Day[0])]
    Mon,
    #[flux::variant(Day[1])]
    Tue,
    #[flux::variant(Day[2])]
    Wed,
}

#[spec(fn (s:State, zig: usize, tag: Day) -> usize[tag])]
pub fn test05(s: State, _zig: usize, _tag: Day) -> usize {
    match s {
        State::On => 1,  //~ ERROR refinement type
        State::Off => 0, //~ ERROR refinement type
    }
}
