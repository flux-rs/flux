pub trait Mono {
    #[flux::sig(fn (zing: &mut i32{v: 0 <= v}))]
    fn foo(z: &mut i32);
}

pub struct Tiger;

impl Mono for Tiger {
    #[flux::sig(fn (pig: &strg i32[@m]) ensures pig: i32[m+1])]
    fn foo(pig: &mut i32) {
        *pig += 1;
    }
}
