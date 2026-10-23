// The output of an `async fn` is desugared into an opaque type, so the refinement parameters
// mentioned in it are early bound. Parameters only mentioned in the inputs are late bound.

// `a` is late bound and `b` is early bound. Since `b` is declared after `a`, its index among the
// early bound parameters is different from its position.
#[flux::sig(async fn(x: i32[@a], y: i32[@b]) -> i32{v: v >= b})]
pub async fn max(x: i32, _y: i32) -> i32 {
    x //~ ERROR refinement type
}

#[flux::sig(async fn() -> i32{v: v >= 6})]
pub async fn use_max() -> i32 {
    max(1, 5).await
} //~ ERROR refinement type
