// Test that we can lift a path segment with `Res::Err` resulting from using `$crate` inside a macro
#[derive(PartialEq, PartialOrd)]
struct S;
