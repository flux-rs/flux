use std::fmt;

#[derive(Clone, Copy, Debug)]
pub struct Argument {
    pos: usize,
    index: usize,
}

impl Argument {
    pub fn new(pos: usize) -> Self {
        Self { pos, index: 0 }
    }

    pub fn pos(&self) -> usize {
        self.pos
    }

    pub(crate) fn index(self) -> usize {
        self.index
    }
}

impl fmt::Display for Argument {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "arg_{}_{}", self.pos, self.index)
    }
}
