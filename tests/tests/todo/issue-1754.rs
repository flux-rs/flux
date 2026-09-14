//! Minimal repro for the ICE fixed by #1757.
//!
//! ```text
//! cargo xtask run tests/tests/todo/issue-1754.rs
//! ```
//!
//! On current main this crashes with:
//!
//! ```text
//! thread 'rustc' panicked at crates/flux-infer/src/infer.rs:415:10:
//! called `Result::unwrap()` on an `Err` value: UnsolvedEvar(?1e)
//! ```

pub trait Buf {
    fn remaining(&self) -> usize;
    fn advance(&mut self, cnt: usize);

    fn get_u8(&mut self) -> usize {
        let n = self.remaining();
        self.advance(1);
        n
    }
}

impl<T: Buf + ?Sized> Buf for &mut T {
    fn remaining(&self) -> usize {
        (**self).remaining()
    }

    fn advance(&mut self, cnt: usize) {
        (**self).advance(cnt)
    }
}
