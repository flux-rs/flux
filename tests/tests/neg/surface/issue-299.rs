#![allow(unused)]

#[flux::refined_by(a: int)]
struct S1 {
    f1: S2,
    #[flux::field(i32[a])]
    f2: i32,
    #[flux::field(i32{v: v > 0})]
    f3: i32,
}

#[flux::refined_by(a: int, b: int)]
struct S2 {
    #[flux::field(i32)]
    pub f1: i32,
    #[flux::field(i32[a])]
    pub f2: i32,
    #[flux::field({i32[b] | b > 0})]
    pub f3: i32,
    #[flux::field(i32{v: v > 0})]
    pub f4: i32,
}

#[flux::refined_by(a: int)]
enum E {
    #[flux::variant((S2) -> E[10])]
    A(S2),
}

fn test02(x: &mut S1) {
    x.f3 -= 1; //~ ERROR assignment
    x.f1.f1 -= 1;
    x.f1.f4 -= 1; //~ ERROR assignment
}

fn test03(x: S2, y: S2) {
    let mut arr = [x, y];
    arr[0].f1 -= 1;
    arr[0].f4 -= 1; //~ ERROR assignment
}

fn test04(x: &mut E) {
    match x {
        E::A(y) => {
            y.f1 -= 1;
            y.f4 -= 1; //~ ERROR assignment
        }
    }
}
