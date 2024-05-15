trait MyTrait {
    type Assoc;

    fn foo(self) -> <Self as MyTrait>::Assoc;
}

impl MyTrait for i32 {
    type Assoc = i32;

    // Test we can lift and convert `Self::Assoc`
    fn foo(self) -> Self::Assoc {
        self
    }
}
