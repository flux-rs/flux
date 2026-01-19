pub trait Message<L>: Sized {
    fn upcast(label: L) -> Self;
    fn downcast(self) -> Result<L, Self>;
}

pub trait Role {
    type Message;
}

pub trait TrySend<T> {
    type Error;
    fn send(&mut self, item: T) -> Result<(), Self::Error>;
}

pub trait Route<R>: Role {
    type Route;
    fn route(&mut self) -> &mut Self::Route;
}

pub struct State<'r, R: Role> {
    role: &'r mut R,
}

pub trait FromState<'r> {
    type Role: Role;
    fn from_state(state: State<'r, Self::Role>) -> Self;
}

pub struct Send<'q, Q: Role, R, L, S: FromState<'q, Role = Q>> {
    state: State<'q, Q>,
    _phantom: core::marker::PhantomData<(R, L, S)>,
}

impl<'q, Q: Role, R, L, S: FromState<'q, Role = Q>> FromState<'q> for Send<'q, Q, R, L, S> {
    type Role = Q;
    fn from_state(state: State<'q, Self::Role>) -> Self {
        Self {
            state,
            _phantom: core::marker::PhantomData,
        }
    }
}

impl<'q, Q: Route<R>, R, L, S: FromState<'q, Role = Q>> Send<'q, Q, R, L, S>
where
    Q::Message: Message<L>,
    Q::Route: TrySend<Q::Message>,
{
    pub fn send(self, label: L) -> Result<S, <Q::Route as TrySend<Q::Message>>::Error> {
        self.state.role.route().send(Message::upcast(label))?;
        Ok(FromState::from_state(self.state))
    }
}

fn main() {}
