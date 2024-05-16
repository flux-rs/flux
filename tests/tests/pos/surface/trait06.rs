trait SuperTrait {
    type AssocSuper;
}

trait MyTrait: SuperTrait {
    type MyAssoc;

    fn foo(x: Self::AssocSuper) -> Self::MyAssoc;
}

impl SuperTrait for i32 {
    type AssocSuper = i32;
}

impl MyTrait for i32 {
    type MyAssoc = i32;

    // Test we can lift and convert `Self::MyAssoc`
    fn foo(x: Self::AssocSuper) -> Self::MyAssoc {
        x
    }
}

fn foo<T: MyTrait>(x: T::AssocSuper, y: T::MyAssoc) {}
