#![feature(extern_types)]

use flux_attrs::*;

#[refined_by(n: int)]
struct S {
    #[field(i32[n])]
    f: i32,
}

#[refined_by(f: T<int>)] //~ Error type parameter expects no generics but found 1
struct X<T> {
    #[field(T[f])]
    f: T,
}

#[assoc(fn foo(x: Self<int>) -> int)] //~ Error type alias Self expects no generics but found 1
trait MyTrait {}

defs! {
    opaque sort MyOpaqueSort;
    opaque sort MyOpaqueSort2<T>;
}

#[opaque]
#[refined_by(f: MyOpaqueSort<int>)] //~ Error opaque sort MyOpaqueSort expects no generics but found 1
struct Y {}

#[opaque]
#[refined_by(f: MyOpaqueSort2<int, int>)] //~ Error opaque sort MyOpaqueSort2 expects exactly one generic argument but found 2
struct Z {}

unsafe extern "C" {
    type A;
}

#[spec(fn(x: &A<i32>))] //~ ERROR generic arguments are not allowed on foreign types
fn test00(x: &A) {}
