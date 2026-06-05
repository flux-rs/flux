use flux_attrs::*;

trait MyTrait {}

impl MyTrait for i32 {}

#[spec(fn() -> i32)] //~ ERROR function has an incompatible refinement annotation
fn foo() -> impl MyTrait {
    0
}
