// Step 1 : declare -------------------------------
#[flux::generics(Self as base)]
#[flux::predicate{ f : (Self) -> bool }]
pub trait MyTrait {
    fn method(&self) -> i32;
}

// Step 2 : implement -----------------------------
#[flux::predicate{ f : |x:int| { 0 < x } }] // TODO: check against trait-def
impl MyTrait for i32 {
    fn method(&self) -> i32 {
        10
    }
}

// Step 3 : abstract ------------------------------
#[flux::trusted] // TODO: subtyping with alias_pred on lhs
#[flux::sig(fn<T as base>(&{T[@x] | <T as MyTrait>::f(x)}))] // TODO: check against trait-spec
pub fn bob<T: MyTrait>(x: &T) {
    x.method();
}

// Step 4 : concretize ----------------------------
pub fn test() {
    let z0 = 0;
    bob(&z0); //~ ERROR refinement type
    let z1 = 1;
    bob(&z1);
}
