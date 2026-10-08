#![flux::defs {
    #[hide]
    fn id<T>(x: T) -> T { //~ ERROR inlined definitions cannot be hidden
        x
    }
}]
