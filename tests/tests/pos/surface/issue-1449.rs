#![allow(unused)]
extern crate flux_rs;
use std::marker::PhantomData;

use flux_rs::attrs::*;

trait Role {
    type Message;
}

trait Route<R>: Role + Sized {
    type Route;
    fn route(&mut self) -> &mut Self::Route;
}

struct State<'r, R: Role> {
    role: &'r mut R,
}

trait FromState<'r> {
    type Role: Role;
    fn from_state(state: State<'r, Self::Role>) -> Self;
}

trait Choice<'r, L> {
    type Session: FromState<'r>;
}

struct Select<'q, Q: Role, R, C> {
    state: State<'q, Q>,
    phantom: PhantomData<(R, C)>,
}

impl<'q, Q: Role, R, C> FromState<'q> for Select<'q, Q, R, C> {
    type Role = Q;
    fn from_state(state: State<'q, Self::Role>) -> Self {
        Self { state, phantom: PhantomData }
    }
}

trait TrySend<T> {
    type Error;
    fn send(&mut self, item: T) -> Result<(), Self::Error>;
}

trait Message<L>: Sized {
    fn upcast(label: L) -> Self;
}

type SendError<Q, R> = <<Q as Route<R>>::Route as TrySend<<Q as Role>::Message>>::Error;

impl<'q, Q: Route<R>, R, C> Select<'q, Q, R, C>
where
    Q::Route: TrySend<Q::Message>,
{
    pub fn select<L>(self, label: L) -> Result<<C as Choice<'q, L>>::Session, SendError<Q, R>>
    where
        Q::Message: Message<L>,
        C: Choice<'q, L>,
        C::Session: FromState<'q, Role = Q>,
    {
        self.state.role.route().send(Message::upcast(label))?;
        Ok(FromState::from_state(self.state))
    }
}

struct End<'r, R: Role> {
    _state: State<'r, R>,
}

impl<'r, R: Role> FromState<'r> for End<'r, R> {
    type Role = R;
    fn from_state(state: State<'r, Self::Role>) -> Self {
        Self { _state: state }
    }
}

struct DummyChannel;

impl<T> TrySend<T> for DummyChannel {
    type Error = ();
    fn send(&mut self, _: T) -> Result<(), ()> {
        Ok(())
    }
}

#[flux_rs::refined_by(val: int)]
struct Correct {
    #[flux_rs::field(i32[val])]
    value: i32,
}

impl Correct {
    #[flux_rs::spec(fn(x: i32[@v], n: i32[@s]) -> Correct[v] requires v == s)]
    fn new(x: i32, _n: i32) -> Self {
        Correct { value: x }
    }
}

enum Label {
    Correct(Correct),
}

impl Message<Correct> for Label {
    fn upcast(c: Correct) -> Self {
        Label::Correct(c)
    }
}

struct B {
    channel: DummyChannel,
}

impl Role for B {
    type Message = Label;
}

struct C;

impl Route<C> for B {
    type Route = DummyChannel;
    fn route(&mut self) -> &mut DummyChannel {
        &mut self.channel
    }
}

enum MyChoice {}

impl<'r> Choice<'r, Correct> for MyChoice {
    type Session = End<'r, B>;
}

fn test_select(s: Select<'_, B, C, MyChoice>, guess: i32, secret: i32) {
    if guess == secret {
        // Triggers the error
        let _ = s.select(Correct::new(guess, secret));
    }
}
