#[flux::reflect]
#[derive(PartialEq, Eq)]
pub enum State {
    On,
    Off,
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

// #[flux::sig(fn (s:State[On]) -> usize[1])]
// pub fn test03(s: State) -> usize {
//     if s == State::On {
//         1
//     } else {
//         0
//     }
// }

#[flux::sig(fn (s:State[On]) -> usize[1])]
pub fn test04(s: State) -> usize {
    match s {
        State::On => 1,
        State::Off => 0,
    }
}
