use flux_attrs::*;

#[extern_spec(core::task)]
#[refined_by(data: ptr)]
struct RawWaker;

#[extern_spec(core::task)]
impl RawWaker {
    // Core impl: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/task/wake.rs#L56
    #[spec(fn(data: *const[@p] (), vtable: &RawWakerVTable) -> RawWaker[p])]
    const fn new(data: *const (), vtable: &'static RawWakerVTable) -> RawWaker;
}

#[extern_spec(core::task)]
#[refined_by(data: ptr)]
struct Waker;

#[extern_spec(core::task)]
impl Waker {
    // Core impl: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/task/wake.rs#L513
    #[spec(fn(data: *const[@p] (), vtable: &RawWakerVTable) -> Waker[p])]
    const unsafe fn new(data: *const (), vtable: &'static RawWakerVTable) -> Self;

    // Core impl: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/task/wake.rs#L532
    #[spec(fn(RawWaker[@data]) -> Waker[data])]
    const unsafe fn from_raw(waker: RawWaker) -> Waker;

    // Core impl: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/task/wake.rs#L567
    #[spec(fn() -> &Waker{w: w.data.addr == 0})]
    const fn noop() -> &'static Waker;

    // Core impl: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/task/wake.rs#L576
    #[spec(fn(&Waker[@data]) -> *const[data] ())]
    fn data(&self) -> *const ();
}
