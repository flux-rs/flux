#[flux::assoc(final fn foo() -> bool { true })] 
#[flux::assoc(fn baz() -> bool)] 
pub trait MyTrait {}

pub struct Baz;

#[flux::assoc(fn foo() -> bool { true })] 
#[flux::assoc(fn baz() -> bool { true })] 
impl MyTrait for Baz {} //~ERROR associated refinement `foo` is final and should not be implemented anywhere other than the trait definition