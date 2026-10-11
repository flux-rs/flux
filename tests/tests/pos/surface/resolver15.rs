// Modules named after builtin sorts do not hide those sorts.
mod int {}
mod bool {}

#[flux::opaque]
#[flux::refined_by(n: int, b: bool)]
struct S;

// A struct can denote a sort and must keep shadowing the builtin.
mod adt {
    use A as int;

    #[flux::refined_by(b: bool)]
    struct A {
        #[flux::field(bool[b])]
        flag: bool,
    }

    #[flux::refined_by(n: int)]
    struct S {
        #[flux::field(int[n])]
        value: int,
    }
}
