pub trait MyTrait {
    #[flux::sig(fn(x: &strg i32) ensures x: i32)]
    fn foo1(x: &mut i32);
}

impl MyTrait for () {
    #[flux::sig(fn(x: &strg i32[@n]) ensures x: i32[n+1])]
    fn foo1(x: &mut i32) {}
}

impl MyTrait for bool {
    #[flux::sig(fn(x: &mut i32{v: 0 <= v}))] //~ ERROR
    fn foo1(x: &mut i32) {}
}

impl MyTrait for usize {
    fn foo1(x: &mut i32) { //~ ERROR
    }
}
