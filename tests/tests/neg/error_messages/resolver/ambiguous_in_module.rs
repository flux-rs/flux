//! A *qualified* path into a module whose own glob re-exports bind the same name to two different
//! items (`mod m { pub use a::*; pub use b::*; }` and then `m::S`) is ambiguous, just like the
//! unqualified case in `resolver13.rs`. rustc reports `E0659` here too.
//!
//! `S` is only ever named from a flux `use`, so rustc never resolves it and reports nothing;
//! detecting the ambiguity is entirely up to us.
#![allow(dead_code, unused_imports, non_snake_case)]

use flux_attrs::*;

mod a {
    pub struct S {}
}

mod b {
    pub struct S {}
}

mod m {
    pub use super::{a::*, b::*};
}

defs! {
    use m::S; //~ ERROR the name `S` is ambiguous
}

// The same ambiguity reached through a qualified path in a signature rather than a flux `use`.
#[spec(fn(x: m::S))] //~ ERROR the name `S` is ambiguous
fn test(_x: i32) {}

// An item defined in `m` itself shadows the globs, but only in *its* namespace: `S` is still
// ambiguous in the type namespace. rustc reports the import too, even though the value namespace
// resolves cleanly to `m::S` the function.
mod shadowed {
    pub use super::{a::*, b::*};

    pub fn S() {}
}

defs! {
    use shadowed::S; //~ ERROR the name `S` is ambiguous
}
