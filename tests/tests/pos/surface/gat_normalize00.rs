// Normalizing a projection on a GAT through an impl: the GAT's own lifetime param follows the
// impl's params in the substitution used to instantiate the associated type.

pub trait Pat: Sized {
    type S<'a>;
    fn into_s<'a>(self, h: &'a str) -> Self::S<'a>;
}

impl Pat for char {
    type S<'a> = &'a str;
    fn into_s<'a>(self, h: &'a str) -> &'a str { h }
}

pub fn g<'a, P: Pat>(p: P, h: &'a str) -> bool {
    let _s = p.into_s(h);   // call returns <P as Pat>::S<'a>
    true
}

pub struct W<'a>(<char as Pat>::S<'a>);
pub fn f<'a>(w: &W<'a>) -> &'a str { w.0 }
