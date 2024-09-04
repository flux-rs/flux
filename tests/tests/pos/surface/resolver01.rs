// Check we can resolve paths inside blocks

mod mymod {
    pub struct S;
}

const _: () = {
    use mymod::S;

    #[flux::sig(fn(x: S))]
    fn test00(x: S) {}
};
