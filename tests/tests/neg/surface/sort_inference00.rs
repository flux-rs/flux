fn test00() {
    #[flux::sig(fn({a,b. (i32[a], i32[b]) | b > a}) -> {v. i32[v] | v > 10})]
    fn f(x: (i32, i32)) -> i32 {
        x.1 - x.0 //~ ERROR refinement type
    }
    f((0, 0)); //~ ERROR refinement type
}

fn test01() {
    #[flux::sig(fn({a. (i32{v: v == a + 1}, i32[a])}))]
    fn f(x: (i32, i32)) {}
    f((1, 1)); //~ ERROR refinement type
}
