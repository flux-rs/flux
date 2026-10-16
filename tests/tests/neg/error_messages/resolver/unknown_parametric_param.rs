// `#[assume_parametric]` on an impl can only name the impl's type params
use flux_attrs::*;

struct S<T> {
    f: T,
}

#[assume_parametric(U)] //~ERROR unknown type parameter
impl<T> S<T> {
    fn get(&self) -> &T {
        &self.f
    }
}
