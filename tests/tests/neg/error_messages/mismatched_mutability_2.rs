pub trait MyTrait {
    #[flux::sig(fn(x: &strg i32) ensures x: i32)]
    fn foo1(x: &mut i32); //~ NOTE the incompatible super-type
}

impl MyTrait for () {
    #[flux::sig(fn(x: &strg i32[@n]) ensures x: i32[n+1])]
    fn foo1(x: &mut i32) {
        *x += 1;
    }
}

impl MyTrait for usize {
    fn foo1(_x: &mut i32) { //~ ERROR incompatible subtyping
    }
}
