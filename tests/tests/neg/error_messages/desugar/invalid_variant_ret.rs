// ignore-test: implement a syntactic check to detect these errors

enum E1<T> {
    #[flux::variant((T) -> E1)] //~ ERROR this enum must take 1 generic argument
    A(T),
}

enum E2<T> {
    #[flux::variant((E1<T>, T) -> E1<T>)] //~ ERROR invalid refinement annotation
    A(E1<T>, T),
}

enum E3<T> {
    #[flux::variant((i32, T) -> E3<i32>)] //~ ERROR invalid refinement annotation
    A(i32, T),
}

enum E4 {
    #[flux::variant((i64) -> E4)] //~ ERROR incompatible refinement annotation
    A(i32),
}
