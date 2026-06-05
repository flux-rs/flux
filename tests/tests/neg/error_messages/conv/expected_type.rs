use flux_attrs::*;

trait A {}

#[spec(fn(x: A))] //~ ERROR expected a type, found trait
fn test00(x: i32) {}

#[allow(non_snake_case)]
mod B {}

#[spec(fn(x: B))] //~ ERROR expected a type, found module
fn test01(x: i32) {}
