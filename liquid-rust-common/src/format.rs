use std::fmt::{self, Write};

pub struct PadAdapter<T> {
    inner: T,
    state: PadAdapterState,
}

#[derive(Clone, Copy)]
pub struct PadAdapterState {
    on_newline: bool,
}

impl<T> PadAdapter<T> {
    fn new(inner: T, state: PadAdapterState) -> Self {
        PadAdapter { inner, state }
    }

    pub fn wrap_on_newline(inner: T) -> Self {
        PadAdapter {
            inner,
            state: PadAdapterState { on_newline: true },
        }
    }
}

impl<'a, W> PadAdapter<&'a mut W> {
    pub fn wrap_fmt(inner: &'a mut W) -> Self
    where
        W: fmt::Write,
    {
        PadAdapter {
            inner,
            state: PadAdapterState { on_newline: false },
        }
    }
}

impl<'a, W> fmt::Write for PadAdapter<&'a mut W>
where
    W: fmt::Write,
{
    fn write_str(&mut self, mut s: &str) -> fmt::Result {
        while !s.is_empty() {
            if self.state.on_newline {
                self.inner.write_str("    ")?;
            }

            let split = match s.find('\n') {
                Some(pos) => {
                    self.state.on_newline = true;
                    pos + 1
                }
                None => {
                    self.state.on_newline = false;
                    s.len()
                }
            };
            self.inner.write_str(&s[..split])?;
            s = &s[split..];
        }

        Ok(())
    }
}

impl<T> fmt::Display for PadAdapter<T>
where
    T: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(PadAdapter::new(f, self.state), "{}", self.inner)
    }
}
