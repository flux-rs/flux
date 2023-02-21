#![allow(unused)]
#![feature(register_tool)]
#![register_tool(flux)]

#[flux::refined_by(a: int)]
struct S1 {
    f1: S2,
    #[flux::field(i32[@a])]
    f2: i32,
    #[flux::field(i32{v: v > 0})]
    f3: i32,
}

#[flux::refined_by(a: int, b: int)]
struct S2 {
    #[flux::field(i32)]
    pub f1: i32,
    #[flux::field(i32[@a])]
    pub f2: i32,
    #[flux::field({i32[@b] : b > 0})]
    pub f3: i32,
    #[flux::field(i32{v: v > 0})]
    pub f4: i32,
}

#[flux::refined_by(a: int)]
enum E1 {
    #[flux::variant((S2) -> E1[10])]
    A(S2),
}

fn test01(x: &S1) {
    let a = x.f2 + 1;
    let b = x.f3 + 1;
    let c = x.f1.f1 + 1;
    let d = x.f1.f2 + 1;
    let e = x.f1.f3 + 1;
    let f = x.f1.f3 + 1;
}

fn test02(x: &mut S1) {
    x.f3 += 1;
    x.f1.f1 += 1;
    x.f1.f4 += 1;
}

fn test03(x: S2, y: S2) {
    let mut arr = [x, y];
    arr[0].f1 += 1;
    arr[0].f4 += 1;
}

fn test04(x: &mut E1) {
    match x {
        E1::A(y) => {
            y.f1 += 1;
            y.f4 += 1;
        }
    }
}

enum E2 {
    A(i32),
}

fn test05(x: &mut E2) -> &mut i32 {
    match x {
        E2::A(y) => y,
    }
}
