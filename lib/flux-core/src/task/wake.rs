use flux_attrs::*;

#[extern_spec(core::task)]
#[refined_by(d_base: int, d_addr: int, d_size: int)]
struct RawWaker;

#[extern_spec(core::task)]
impl RawWaker {
    // Core impl: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/task/wake.rs#L56
    #[spec(fn(data: *const[@p] (), vtable: &RawWakerVTable) -> RawWaker[p.base, p.addr, p.size])]
    const fn new(data: *const (), vtable: &'static RawWakerVTable) -> RawWaker;
}

#[extern_spec(core::task)]
#[refined_by(d_base: int, d_addr: int, d_size: int)]
struct Waker;

#[extern_spec(core::task)]
impl Waker {
    // Core impl: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/task/wake.rs#L513
    #[spec(fn(data: *const[@p] (), vtable: &RawWakerVTable) -> Waker[p.base, p.addr, p.size])]
    const unsafe fn new(data: *const (), vtable: &'static RawWakerVTable) -> Self;

    // Core impl: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/task/wake.rs#L532
    #[spec(fn(RawWaker[@d_base, @d_addr, @d_size]) -> Waker[d_base, d_addr, d_size])]
    const unsafe fn from_raw(waker: RawWaker) -> Waker;

    // Core impl: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/task/wake.rs#L567
    #[spec(fn() -> &Waker{w: w.d_addr == 0})]
    const fn noop() -> &'static Waker;

    // Core impl: https://github.com/rust-lang/rust/blob/7517636f510adf0a797e10cf655c21c0eb0723fb/library/core/src/task/wake.rs#L576
    #[spec(fn(&Waker[@d_base, @d_addr, @d_size]) -> *const[d_base, d_addr, d_size] ())]
    fn data(&self) -> *const ();
}
