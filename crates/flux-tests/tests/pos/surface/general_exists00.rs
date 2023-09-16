#![feature(register_tool)]
#![register_tool(flux)]

// Existential without a constraint
fn test00() {
    #[flux::sig(fn({a:int. i32[a]}))]
    fn f(x: i32) {}

    f(0);
}

// Existential nested with a constraint tpye
fn test01() {
    #[flux::sig(fn({a:int. {i32[a] | a > 0}}) -> i32{v: v >= 0})]
    fn f(x: i32) -> i32 {
        x
    }

    f(1);
}

// Existential with constraint
fn test02() {
    #[flux::sig(fn({a:int. i32[a] | a > 0}) -> i32{v: v >= 0})]
    fn f(x: i32) -> i32 {
        x
    }
    f(1);
}

// Nested existentials
fn test03() {
    #[flux::sig(fn({a:int. {b:int. (i32[a], i32[b]) | b > a } }) -> i32{v: v > 0})]
    fn f(x: (i32, i32)) -> i32 {
        x.1 - x.0
    }
    f((0, 1));
}

// general existential nested with "limited" existential
fn test04() {
    #[flux::sig(fn({a:int. (i32[a], i32{b: b > a})}) -> i32{v: v > 0})]
    fn f(x: (i32, i32)) -> i32 {
        x.1 - x.0
    }

    f((0, 1));
}

// Multi param existential
fn test05() {
    #[flux::sig(fn({ a:int,b:int. (i32[a], i32[b]) | b > a }) -> i32{v: v > 0})]
    fn f(x: (i32, i32)) -> i32 {
        x.1 - x.0
    }
    f((0, 1));
}
