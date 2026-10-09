#[flux::refined_by(present: bool)]
pub enum Maybe<T> {
    #[flux::variant(Maybe<T>[false])]
    Nothing,
    #[flux::variant((T) -> Maybe<T>[true])]
    Just(T),
}

use Maybe::Nothing;

#[flux::spec(fn() -> Maybe<u8>[Nothing])] //~ ERROR enum variant cannot be used as a refinement value
pub fn unqualified() -> Maybe<u8> {
    Nothing
}

#[flux::spec(fn() -> Maybe<u8>[Maybe::Nothing])] //~ ERROR enum variant cannot be used as a refinement value
pub fn qualified() -> Maybe<u8> {
    Nothing
}

#[flux::refined_by(present: bool)]
pub enum State {
    #[flux::variant(State[false])]
    Empty,
    #[flux::variant(State[true])]
    Full,
}

#[flux::spec(fn() -> State[State::Empty])] //~ ERROR enum variant cannot be used as a refinement value
pub fn non_generic() -> State {
    State::Empty
}

#[flux::reflect]
pub enum Reflected {
    A,
    B,
}

#[flux::spec(fn() -> bool[Reflected::A])] //~ ERROR mismatched sorts
pub fn reflected_wrong_sort() -> bool {
    true
}

#[flux::reflect]
pub enum Other {
    A,
    B,
}

#[flux::spec(fn() -> Reflected[Other::A])] //~ ERROR mismatched sorts
pub fn reflected_wrong_enum() -> Reflected {
    Reflected::A
}
