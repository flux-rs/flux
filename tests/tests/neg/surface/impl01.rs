pub trait Mono {
    #[flux::sig(fn (zing: &strg i32[@n]) ensures zing: i32{v:n < v})]
    fn foo(z: &mut i32);
}

pub struct Horse;

impl Mono for Horse {
    #[flux::sig(fn (z: &strg i32[@n]) ensures z: i32{v:v < n})]
    fn foo(z: &mut i32) {
        //~^ ERROR refinement type
        *z -= 1;
    }
}
