#[flux::sig(fn(bool[true]))]
pub fn assert(_: bool) {}

// Test that we support async function returning unit
#[flux::sig(async fn())]
pub async fn test() {
    let x = make_nat().await;
    assert(x >= 0);
}

#[flux::sig(async fn() -> i32{v: v >= 0})]
pub async fn make_nat() -> i32 {
    0
}

// Test that we support async function returning unit
#[flux::sig(async fn())]
pub async fn test_res() {
    let x = make_nat_res().await;
    x.map_err(|_| ()).unwrap();
}

#[flux::sig(async fn() -> Result<i32{v: v >= 0}, ()>)]
pub async fn make_nat_res() -> Result<i32, ()> {
    Ok(0)
}
