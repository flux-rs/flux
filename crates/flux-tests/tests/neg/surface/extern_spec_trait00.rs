use flux_rs::extern_spec;

// the "existing" trait
pub trait MyTrait {
    fn method(&self) -> Self;
}

// the "extern" spec
#[extern_spec]
#[flux::generics(Self as base)]
#[flux::predicate(f: (Self) -> bool)]
trait MyTrait {}

// // the "generated" wrapper trait
// #[flux::extern_spec]
// #[flux::generics(Self as base)]
// #[flux::predicate(f: (Self) -> bool)]
// trait __FluxExternTraitMyTrait: MyTrait {}

// -----------------------------------------------------------------------------------
// client code
// -----------------------------------------------------------------------------------

#[flux::trusted]
#[flux::sig(fn<T as base>(&T{v: <T as MyTrait>::f(v)}) -> T{v: <T as MyTrait>::f(v)})]
pub fn lib<T: MyTrait>(x: &T) -> T {
    x.method()
}

#[flux::sig(fn<T as base>(&T{v: <T as MyTrait>::f(v)}) -> T{v: <T as MyTrait>::f(v)})]
pub fn cli<T: MyTrait>(x: &T) -> T {
    lib(x)
}

#[flux::sig(fn<T as base>(&T) -> T{v: <T as MyTrait>::f(v)})]
pub fn cli2<T: MyTrait>(x: &T) -> T {
    lib(x) //~ ERROR refinement type error
}
