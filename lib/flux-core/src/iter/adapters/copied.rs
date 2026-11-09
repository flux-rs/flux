use flux_attrs::*;

#[extern_spec(core::iter)]
#[refined_by(inner: I)]
struct Copied<I>;

#[extern_spec(core::iter)]
#[assoc(
    fn size(x: Copied<I>) -> int { <I as Iterator>::size(x.inner) }
    fn done(x: Copied<I>) -> bool { <I as Iterator>::done(x.inner) }
    fn step(x: Copied<I>, y: Copied<I>) -> bool { <I as Iterator>::step(x.inner, y.inner) }
)]
impl<'a, I: Iterator<Item = &'a T>, T: 'a + Copy> Iterator for Copied<I> {
    #[spec(fn(self: &mut Self[@curr_s]) -> Option<T>[!<Self as Iterator>::done(curr_s)]
           ensures self: Self{next_s: <Self as Iterator>::step(curr_s, next_s)})]
    fn next(&mut self) -> Option<T>;
}
