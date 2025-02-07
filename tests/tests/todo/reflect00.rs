#[flux::reflect]
pub enum State {
    On,
    Off,
}

#[flux::refined_by(day: int)]
pub enum Day {
    #[flux::variant(Day[0])]
    Mon,
    #[flux::variant(Day[1])]
    Tue,
    #[flux::variant(Day[2])]
    Wed,
}

// #[flux_rs::sig(fn () -> State[On])]
// pub fn test00() -> State {
//     State::On
// }

// #[flux_rs::sig(fn () -> State[Off])]
// pub fn test01() -> State {
//     State::Off
// }

// #[flux::sig(fn () -> State[Off])]
// pub fn test02() -> State {
//     State::On //~ ERROR refinement type
// }

// #[flux::sig(fn (State[@squig], zig: usize, tag: Day) -> usize[tag])]
// pub fn test04(s: State, zig: usize, tag: Day) -> usize {
//     match s {
//         State::On => 1,  //~ ERROR refinement type
//         State::Off => 0, //~ ERROR refinement type
//     }
// }

#[flux::sig(fn (s:State, zig: usize, tag: Day) -> usize[tag])]
pub fn test05(s: State, zig: usize, tag: Day) -> usize {
    match s {
        State::On => 1,
        State::Off => 0,
    }
}
