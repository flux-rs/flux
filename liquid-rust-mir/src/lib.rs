#![feature(rustc_private)]

extern crate rustc_span;

mod bblock;
mod func;
mod local;
mod operand;
mod program;
mod rvalue;
mod statement;
mod terminator;
pub mod ty;

pub use bblock::{BBlock, BBlockBuilder, BBlockId};
pub use func::{Func, FuncBuilder, FuncId};
pub use local::Local;
pub use operand::Operand;
pub use program::Program;
pub use rvalue::Rvalue;
pub use statement::{Statement, StatementKind};
pub use terminator::{Terminator, TerminatorKind};

pub use rustc_span::{Span, DUMMY_SP};
