#![allow(unused)]

trait FromState {
    type Role;
}

trait Choice {
    type Session: FromState;
}

struct End<R>(R);

struct B;

struct MyChoice {}

impl<R> FromState for End<R> {
    type Role = R;
}

impl Choice for MyChoice {
    type Session = End<B>;
}

fn select<Q, C>()
where
    C: Choice,
    C::Session: FromState<Role = Q>,
{
}

fn test_select() {
    select::<B, MyChoice>();
}

