trait MyTrait {}

impl MyTrait for i32 {}

#[flux_rs::spec(fn() -> i32)] //~ ERROR function has an incompatible refinement annotation
fn foo() -> impl MyTrait {
    0
}
