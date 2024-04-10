#[flux::sig(fn(bool[true]))]
pub fn assert(_b: bool) {}

#[flux::sig(async fn (y:i32{v:0<=v}) -> i32{v:v <= 1000})]
pub async fn bar(y: i32) -> i32 {
    let z = if y > 10 { 1 } else { 0 };
    assert(z >= 0);
    assert(y >= 0);
    z + 999
}

#[flux::sig(async fn (y:i32{v:0<=v}) -> i32{v:v < 1000 })]
pub async fn foo(y: i32) -> i32 {
    let z = if y > 10 { 1 } else { 0 };
    assert(z >= 0);
    assert(y >= 0);
    z + 999 //~ ERROR refinement type
}

#[flux::sig(async fn () -> i32{v:v < 1500 })]
pub async fn jazz() -> i32 {
    let apple = bar(10).await;
    let banana = bar(20).await;
    apple + banana //~ ERROR refinement type
}

#[flux::sig(async fn () -> i32{v:v <= 2000 })]
pub async fn pizzazz() -> i32 {
    let apple = bar(10).await;
    let banana = bar(20).await;
    apple + banana
}

#[flux::sig(async fn (y:i32) -> i32{v:y<v} requires 0 <= y)]
pub async fn bar1(y: i32) -> i32 {
    let z = if y > 10 { 1 } else { 0 };
    assert(z >= 0);
    assert(y >= 0);
    y + z //~ ERROR refinement type
}

#[flux::sig(async fn (k:i32) -> i32{v:k<=v} )]
pub async fn jazz1(k: i32) -> i32 {
    let apple = bar1(k).await; //~ ERROR refinement type
    let banana = bar1(apple).await; //~ ERROR refinement type
    banana
}
