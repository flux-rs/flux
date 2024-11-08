use flux_rs::*;

#[refined_by(n: int)]
struct S {
    #[field(i32[n])]
    f: i32,
}

defs! {
    fn foo(s: S<int>) -> int { //~ Error sorts associated with this struct should have no generic arguments but 1 generic argument supplied
        s.n
    }

    fn foo2(x: int<bool>) -> int { //~ Error primitive sort int expects no generics but found 1
        1
    }

    fn foo3(x: Map<int>) -> int { //~ Error primitive sort Map expects exactly 2 generic arguments but found 1
        1
    } 

    fn foo4(x: Map) -> int { //~ Error primitive sort Map expects exactly 2 generic arguments but found 0
        1
    }

    fn foo5(x: Set<int, int>) -> int { //~ Error primitive sort Set expects exactly one generic argument but found 2
        1
    }

    fn foo6(x: real<bool>) -> real { //~ Error primitive sort real expects no generics but found 1
        1
    }

    fn foo7(x: bool<int>) -> real { //~ Error primitive sort bool expects no generics but found 1
        1
    }
}

#[flux::refined_by(f: T<int>)] //~ Error type parameter expects no generics but found 1
struct X<T> { 
    #[flux::field(T[f])]
    f: T 
}

#[flux::assoc(fn foo(x: Self<int>) -> int)] //~ Error type alias Self expects no generics but found 1
trait MyTrait {}

flux_rs::defs! {
    opaque sort MyOpaqueSort;
}

#[flux_rs::opaque]
#[flux_rs::refined_by(f: MyOpaqueSort<int>)] //~ Error user defined opaque sorts have no generics but found 1
struct Y {}
