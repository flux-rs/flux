//@run-rustfix
//@normalize-stderr-test: "(?s).*" -> ""
//@rustfix-only-machine-applicable
//@compile-flags: -Fsuggestions=true -Ffix-suggestions
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
    needs_ready(state);
}

#[flux::no_suggestions]
pub fn suggested_witness() {
    repro(State::Ready);
}
