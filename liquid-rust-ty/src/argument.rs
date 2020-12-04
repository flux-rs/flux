use std::fmt;

/// The argument of a dependent function type.
///
/// This type is a de Bruijn index representation of a function's argument.
#[derive(Clone, Copy, Debug)]
pub struct Argument {
    pos: usize,
    index: usize,
}

impl Argument {
    /// Create a new argument with a specific position and de Bruijn index zero.
    pub fn new(pos: usize) -> Self {
        Self { pos, index: 0 }
    }

    /// Return the zero-based position of the argument inside its function, e.g the position of `y`
    /// in `fn(x: usize, y: usize) -> usize` is `1`.
    pub fn pos(&self) -> usize {
        self.pos
    }

    /// Consume the argument and return its de Bruijn index.
    pub(crate) fn index(self) -> usize {
        self.index
    }

    /// Increase the index of the argument by `offset`
    pub fn inc(mut self, offset: usize) -> Self {
        self.index += offset;
        self
    }
}

impl fmt::Display for Argument {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "arg_{}_{}", self.pos, self.index)
    }
}
