#[flux::sig(fn(f: F) -> i32[100]
            where F: FnOnce(x: i32[@n]) -> i32[n + 1] requires n >= 0)]
#[flux::trusted]
fn apply_fn_once<F>(f: F) -> i32
where
    F: FnOnce(i32) -> i32,
{
    let _ = f;
    unimplemented!()
}

#[flux::sig(fn() -> i32[100])]
pub fn client_bad() -> i32 {
    apply_fn_once(|x| x + 2) //~ ERROR refinement type
}
