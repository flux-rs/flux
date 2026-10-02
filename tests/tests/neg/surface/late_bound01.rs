// Late bound refinement parameters whose sorts mention projections.
//
// When checking an impl against the trait, the trait method's signature is instantiated with `S`,
// so the sorts of its late bound parameters become `<S as Trait>::Assoc`. They must be normalized
// to `bool` before the parameters are given names.

pub trait Trait {
    type Assoc;

    #[flux::sig(fn(x: Self::Assoc) -> Self::Assoc[x])]
    fn id(x: Self::Assoc) -> Self::Assoc;

    #[flux::sig(fn[hrn p: Self::Assoc -> bool](x: Self::Assoc{v: p(v)}) -> Self::Assoc{v: p(v)})]
    fn id_hrn(x: Self::Assoc) -> Self::Assoc;
}

pub struct S;

impl Trait for S {
    type Assoc = bool;

    #[flux::sig(fn(x: bool) -> bool[x])]
    fn id(x: bool) -> bool {
        !x //~ ERROR refinement type
    }

    #[flux::sig(fn[hrn p: bool -> bool](x: bool{v: p(v)}) -> bool{v: p(v)})]
    fn id_hrn(x: bool) -> bool {
        x
    }
}

#[flux::sig(fn(x: bool) -> bool[!x])]
pub fn call_id(x: bool) -> bool {
    S::id(x) //~ ERROR refinement type
}

#[flux::sig(fn(x: bool) -> bool[!x])]
pub fn call_id_generic<T: Trait<Assoc = bool>>(x: bool) -> bool {
    T::id(x) //~ ERROR refinement type
}

#[flux::sig(fn(x: bool) -> bool{v: v})]
pub fn call_id_hrn(x: bool) -> bool {
    S::id_hrn(x) //~ ERROR refinement type
}

#[flux::sig(fn(x: bool) -> bool{v: v})]
pub fn call_id_hrn_generic<T: Trait<Assoc = bool>>(x: bool) -> bool {
    T::id_hrn(x) //~ ERROR refinement type
}
