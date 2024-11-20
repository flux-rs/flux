pub trait Mono {
    #[flux::sig(fn (zing: &mut i32{v: 0 <= v}))]
    fn foo(z: &mut i32);
}

pub struct Snake;

impl Mono for Snake {
    #[flux::sig(fn (hog: &strg i32[@m]) ensures hog: i32[m-1])]
    fn foo(hog: &mut i32) {
        //~^ ERROR: type invariant may not hold
        *hog -= 1;
    }
}
