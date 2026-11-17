use flux_attrs::*;

#[extern_spec(core::iter)]
#[refined_by(inner: I)]
struct Cloned<I>;

#[extern_spec(core::iter)]
#[assoc(
    fn size(x: Cloned<I>) -> int { <I as Iterator>::size(x.inner) }
    fn done(x: Cloned<I>) -> bool { <I as Iterator>::done(x.inner) }
    fn step(x: Cloned<I>, y: Cloned<I>) -> bool { <I as Iterator>::step(x.inner, y.inner) }
)]
impl<'a, I: Iterator<Item = &'a T>, T: 'a + Clone> Iterator for Cloned<I> {
    #[spec(fn(self: &mut Self[@curr_s]) -> Option<T>[!<Self as Iterator>::done(curr_s)]
           ensures self: Self{next_s: <Self as Iterator>::step(curr_s, next_s)})]
    fn next(&mut self) -> Option<T>;
}
