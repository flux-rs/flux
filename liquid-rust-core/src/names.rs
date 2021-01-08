#[derive(Clone, Copy, PartialEq, Debug, Eq, Hash)]
pub struct Location<S = usize>(pub S);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct Field<S = usize>(pub S);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct Local<S = usize>(pub S);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct ContId<S = usize>(pub S);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct FnId<S = usize>(pub S);
