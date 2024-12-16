#[flux::sig(fn(x: i32<i32>))] //~ ERROR generic arguments are not allowed on builtin type
fn test00() {}

#[flux::sig(fn(x: T<i32>))] //~ ERROR generic arguments are not allowed on type parameter
fn test01<T>() {}

struct S;

impl S {
    #[flux::sig(fn(Self<i32>))] //~ ERROR generic arguments are not allowed on self type
    fn test02() {}
}

trait MyTrait {
    #[flux::sig(fn(Self<i32>))] //~ ERROR generic arguments are not allowed on self type
    fn test03();
}
