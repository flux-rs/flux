pub trait Mono {
    #[flux::sig(fn (zing: &strg i32[@n]) ensures zing: i32{v:n < v})]
    fn foo(z: &mut i32);
}

pub struct Tiger;

impl Mono for Tiger {
    #[flux::sig(fn (pig: &strg i32[@m]) ensures pig: i32{v:m < v})]
    fn foo(pig: &mut i32) {
        *pig += 1;
    }
}

pub struct Snake;

impl Mono for Snake {
    #[flux::sig(fn (pig: &strg i32[@m]) ensures pig: i32[m+1])]
    fn foo(pig: &mut i32) {
        *pig += 1;
    }
}
