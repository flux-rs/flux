// A path that resolves in the type namespace but does not denote a sort must be reported by
// `conv_sort_path` (which now owns sort-admissibility) rather than panicking with `bug!`.

pub type Alias = i32;

#[flux::refined_by(x: i32)] //~ ERROR expected a sort
pub struct UsePrimTy;

#[flux::refined_by(x: Alias)] //~ ERROR expected a sort
pub struct UseAlias;
