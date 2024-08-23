trait MyTrait {
    type Assoc;
    fn method(&self) -> Self::Assoc;
}

fn test(x: &dyn MyTrait<Assoc = i32>) -> i32 {
    x.method()
}
