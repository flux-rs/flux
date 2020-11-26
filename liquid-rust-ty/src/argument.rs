use std::fmt;

#[derive(Clone, Copy, Debug)]
pub struct Argument {
    pos: usize,
    level: usize,
}

impl Argument {
    pub fn new(pos: usize, level: usize) -> Self {
        Self { pos, level }
    }

    pub fn pos(&self) -> usize {
        self.pos
    }

    pub fn level(&self) -> usize {
        self.level
    }
}

impl fmt::Display for Argument {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "arg_{}_{}", self.pos, self.level)
    }
}
