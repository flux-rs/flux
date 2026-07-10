type Unit = ();

#[flux_rs::spec(fn(a : &mut i32[@foo]) -> Result<Unit { v : (new_foo == foo + 10)}, Unit>
    ensures a : i32[#new_foo]
)]
fn test(a: &mut i32) -> Result<Unit, Unit> {
    *a += 10;
    Ok(())
}
