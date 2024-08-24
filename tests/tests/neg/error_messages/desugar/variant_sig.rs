enum E1<T> {
    #[flux::variant((i32, T) -> i32)] //~ ERROR invalid variant return type
    A(i32, T),
}
