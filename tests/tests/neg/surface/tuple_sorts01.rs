use flux_rs::attrs::*;

defs! {
  fn foo(a: (int, int)) -> int { a.0 + a.1 }
}

#[opaque]
#[refined_by(p: (int, int))]
struct Goober();

#[trusted]
#[spec(fn () -> Goober[(10, 20)])]
fn make_goober() -> Goober {
    Goober()
}

#[spec(fn () -> Goober{v: foo(v) == 1234})]
fn test() -> Goober {
    make_goober() //~ ERROR: refinement type
}
