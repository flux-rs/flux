// compile-flags: -Fsuggestions=true -Ffix-suggestions
// check-suggestions: 1
// suggestion: requires state == crate::State::Ready
// Enum constructors must use variant names, not numeric variant indices.

#[flux::reflect]
pub enum State {
    Ready,
    Done,
}

#[flux::trusted]
#[flux::sig(fn(State[State::Ready]))]
fn needs_ready(state: State) {}

#[flux::sig(fn(State))]
pub fn repro(state: State) {
    needs_ready(state); //~ ERROR refinement type error
}

#[cfg(flux_test_suggestions_applied)]
pub fn suggested_witness() {
    repro(State::Ready);
}
