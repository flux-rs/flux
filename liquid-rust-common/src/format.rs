use std::fmt;

pub struct PadAdapter<T> {
    inner: T,
    width: u32,
    state: PadAdapterState,
}

#[derive(Clone, Copy)]
pub struct PadAdapterState {
    on_newline: bool,
}

impl<'a, W> PadAdapter<&'a mut W> {
    pub fn wrap_fmt(inner: &'a mut W, width: u32) -> Self
    where
        W: fmt::Write,
    {
        PadAdapter { inner, state: PadAdapterState { on_newline: false }, width }
    }
}

impl<'a, W> fmt::Write for PadAdapter<&'a mut W>
where
    W: fmt::Write,
{
    fn write_str(&mut self, mut s: &str) -> fmt::Result {
        while !s.is_empty() {
            if self.state.on_newline {
                for _ in 0..self.width {
                    self.inner.write_str(" ")?;
                }
            }

            let split = if let Some(pos) = s.find('\n') {
                self.state.on_newline = true;
                pos + 1
            } else {
                self.state.on_newline = false;
                s.len()
            };
            self.inner.write_str(&s[..split])?;
            s = &s[split..];
        }

        Ok(())
    }
}
