use flux_rs::attrs::*;

defs! {
  fn foo(a: int, b: int) -> int { a + b }
}

#[opaque]
#[refined_by(p: int)]
struct Goober();

#[trusted]
#[spec(fn () -> Goober[10])]
fn make_goober() -> Goober {
    Goober()
}

#[spec(fn () -> Goober{v: foo(v, v) == 20})]
fn test() -> Goober {
    make_goober()
}
