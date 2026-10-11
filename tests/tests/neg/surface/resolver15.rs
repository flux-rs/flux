mod int {}

// A `crate::`-qualified path explicitly selects the module.
#[flux::refined_by(n: crate::int)] //~ ERROR expected a sort, found module
struct Qualified;

// Falling back to a builtin must still check its generic arguments.
#[flux::refined_by(n: int<bool>)] //~ ERROR primitive sort int expects no generics but found 1
struct BadArgs;

// We only fallback for modules (like rustc), so type aliases still shadow sorts.
mod alias {
    type A = i32;
    use A as int;

    #[flux::refined_by(n: int)] //~ ERROR expected a sort, found type alias
    struct S;
}

// Ordinary prelude types do not get the primitive fallback.
#[allow(non_snake_case)]
mod String {}

#[flux::spec(fn(x: String))] //~ ERROR expected a type, found module
fn ordinary_prelude(x: std::string::String) {}
