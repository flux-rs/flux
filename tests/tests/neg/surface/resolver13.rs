//! Two competing glob imports binding the same name to two *different* items are not an error at
//! import time; the ambiguity is deferred to the first use of the name, matching rustc's `E0659`
//! (<https://doc.rust-lang.org/reference/names/name-resolution.html>).
//!
//! `S` is only ever mentioned inside a flux annotation, so rustc never resolves it and reports
//! nothing here — detecting the ambiguity is entirely up to us.
//!
//! The *qualified* form of the same thing — a path into a module whose own glob re-exports are
//! ambiguous (`mod m { pub use a::*; pub use b::*; }` and then `m::S`) — is covered by
//! `neg/error_messages/resolver/ambiguous_in_module.rs`.
#![allow(unused_imports, dead_code)]

mod a {
    pub struct S;
}

mod b {
    pub struct S;
}

mod two_globs {
    use super::{a::*, b::*};

    #[flux::sig(fn(x: S) -> i32)] //~ ERROR the name `S` is ambiguous
    fn test(x: i32) -> i32 {
        x
    }
}
