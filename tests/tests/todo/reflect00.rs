// #[flux_rs::reflect]
pub enum State {
    On,
    Off,
}

// #[flux_rs::sig(fn () -> State[On])]
// pub fn test00() -> State {
//     State::On
// }

#[flux_rs::sig(fn () -> State[On])]
pub fn test01() -> State {
    State::Off //~ ERROR refinement type
}

// #[flux_rs::sig(fn (s:State[On]) -> usize[1])]
// pub fn test02(s: State) -> usize {
//     match s {
//         State::On => 1,
//         State::Off => 0,
//     }
// }

// // #[flux_rs::sig(fn () -> State[Off])]
// pub fn test01() -> State {
//     State::Off
// }
