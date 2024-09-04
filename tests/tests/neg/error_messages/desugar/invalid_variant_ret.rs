enum E1<T> {
    #[flux::variant((T) -> E1)] //~ ERROR invalid variant return type
    A(T),
}

enum E2<T> {
    #[flux::variant((E1<T>, T) -> E1<T>)] //~ ERROR invalid variant return type
    A(E1<T>, T),
}

enum E3<T> {
    #[flux::variant((i32, T) -> E3<i32>)] //~ ERROR invalid variant return type
    A(i32, T),
}
