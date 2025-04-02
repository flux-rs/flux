use flux_rs::attrs::*;

#[opaque]
#[refined_by(x: T)]
struct S1<T>(T);

#[trusted]
impl<T> S1<T> {
    #[sig(fn(&Self[@r]) -> &T[r])]
    fn get(&self) -> &T {
        &self.0
    }
}

trait Trait {
    type Assoc;
}

fn test<T: Trait>(s: S1<T::Assoc>) {
    s.get();
    flux_rs::assert(false); //~ ERROR refinement type error
}
