#![feature(register_tool, custom_inner_attributes)]
#![register_tool(flux)]

#[path = "../../lib/ghost_cell.rs"]
mod ghost_cell;

use ghost_cell::{GhostCell, GhostToken};

#[flux::sig(fn() -> i32{v: v > 0})]
pub fn test() -> i32 {
    let mut token = GhostToken::new();
    let mut token2 = GhostToken::new();
    let v = GhostCell::new(42, &token);
    let p = (&v, &v);
    *p.0.borrow_mut(&mut token) += 1;
    *p.1.borrow_mut(&mut token2) += 1; //~ ERROR precondition

    v.into_inner()
}
