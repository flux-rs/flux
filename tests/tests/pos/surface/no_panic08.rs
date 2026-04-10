#[flux_rs::refined_by(n: int)]
pub enum State {
    #[flux_rs::variant(State[0])]
    Good,
    #[flux_rs::variant(State[1])]
    Bad,
}

#[flux_rs::refined_by(state: State)]
#[flux_rs::opaque]
struct Foo;

impl Drop for Foo {
    #[flux_rs::sig(fn(&mut Self[@s]))]
    #[flux_rs::no_panic_if(s != State::Bad)] // `s` should be a `State`, but my changes seem to have made it a `Foo`...
    fn drop(&mut self) {}
}
