pub struct Splat<'a, T: 'a, P>
where
    P: FnMut(&T) -> bool,
{
    pub v: &'a [T],
    pub pred: P,
}

impl<'a, T: 'a, P: FnMut(&T) -> bool> Splat<'a, T, P> {
    pub fn now(slice: &'a [T], pred: P) -> Self {
        Self { v: slice, pred }
    }
}
