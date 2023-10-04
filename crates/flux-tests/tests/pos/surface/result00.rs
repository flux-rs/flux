#[flux::sig(fn() -> Result<i32[0], ()>)]
fn baz() -> Result<i32, ()> {
    Ok(0)
}

#[flux::sig(fn() -> Result<i32[1], ()>)]
pub fn baz_call() -> Result<i32, ()> {
    let r = baz()?;
    Ok(r + 1)
}
