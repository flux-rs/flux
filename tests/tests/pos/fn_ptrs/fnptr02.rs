fn test00<T>(x: T) {}

fn test01(x: fn(&i32) -> i32) {
    test00(x);
}
