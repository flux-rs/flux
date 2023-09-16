#![feature(register_tool)]
#![register_tool(flux)]

trait Trait {}

impl Trait for i32 {}

fn foo() -> impl Trait {
    1
}
