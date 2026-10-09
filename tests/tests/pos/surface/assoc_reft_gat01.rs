// Fields and method calls whose type is a projection of a generic associated type

pub trait Searcher {
    fn next(&mut self) -> usize;
}

pub trait Pat: Sized {
    type S<'a>: Searcher;
}

pub struct CS<'a> {
    pub h: &'a str,
}

impl Searcher for CS<'_> {
    fn next(&mut self) -> usize {
        self.h.len()
    }
}

impl Pat for char {
    type S<'a> = CS<'a>;
}

pub struct W<'a>(<char as Pat>::S<'a>);

impl Searcher for W<'_> {
    fn next(&mut self) -> usize {
        self.0.next()
    }
}

pub fn read<'a>(w: &W<'a>) -> &'a str {
    w.0.h
}
