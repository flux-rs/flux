#![feature(extern_types)]

use flux_rs::attrs::*;

#[refined_by(n: int)]
struct S {
    #[field(i32[n])]
    f: i32,
}

#[flux::refined_by(f: T<int>)] //~ Error type parameter expects no generics but found 1
struct X<T> {
    #[flux::field(T[f])]
    f: T,
}

#[flux::assoc(fn foo(x: Self<int>) -> int)] //~ Error type alias Self expects no generics but found 1
trait MyTrait {}

flux_rs::defs! {
    opaque sort MyOpaqueSort;
    opaque sort MyOpaqueSort2<T>;
}

#[flux_rs::opaque]
#[flux_rs::refined_by(f: MyOpaqueSort<int>)] //~ Error opaque sort MyOpaqueSort expects no generics but found 1
struct Y {}

#[flux_rs::opaque]
#[flux_rs::refined_by(f: MyOpaqueSort2<int, int>)] //~ Error opaque sort MyOpaqueSort2 expects exactly one generic argument but found 2
struct Z {}

unsafe extern "C" {
    type A;
}

#[sig(fn(x: &A<i32>))] //~ ERROR generic arguments are not allowed on foreign types
fn test00(x: &A) {}
