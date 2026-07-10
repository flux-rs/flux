use flux_rs::assert;

pub fn foo(x: usize) -> usize {
    assert(x > 100);
    x + 1
}

#[flux::specs {

    #[trusted]
    fn foo(x: usize) -> usize;


}]
const _: () = ();
