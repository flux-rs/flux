use flux_rs::attrs::*;

// Step 1 : declare -------------------------------
pub trait MyTrait {
    #![reft(fn f(self: Self) -> bool)]

    fn method(&self) -> i32;
}

// Step 2 : implement -----------------------------
impl MyTrait for i32 {
    #![reft(fn f(x: int) -> bool { 0 < x } )] // TODO: check against trait-def

    fn method(&self) -> i32 {
        10
    }
}

// Step 3 : abstract ------------------------------
#[trusted] // TODO: subtyping with alias_pred on lhs
#[sig(fn<T as base>(&{T[@x] | <T as MyTrait>::f(x)}))] // TODO: check against trait-spec
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
