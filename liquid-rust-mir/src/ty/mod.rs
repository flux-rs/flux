//! Types and functions used to represent and manipulate refined types inside liquid rust.
//!
//! Several types in this crate are generic over a `V` type parameter to be able to map the
//! variables inside predicates easily.
mod argument;
mod base_ty;
mod int_sign;
mod int_size;
mod literal;
mod op;
mod predicate;
mod ty;
mod variable;

pub use argument::Argument;
pub use base_ty::BaseTy;
pub use int_sign::IntSign;
pub use int_size::IntSize;
pub use literal::Literal;
pub use op::{BinOp, UnOp};
pub use predicate::{Hole, HoleId, Predicate};
pub use ty::{FuncTy, Ty};
pub use variable::{Ghost, Variable};
