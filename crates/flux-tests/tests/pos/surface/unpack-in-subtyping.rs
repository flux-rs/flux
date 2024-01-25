#[flux::sig(fn(Option<{a. (i32[a], {b. {i32[b] | a > b}})}>))]
fn f1(p: Option<(i32, i32)>) {
    f2(p)
}

#[flux::sig(fn(Option<{a,b:int. ({i32[a] | b < a}, i32[b])}>))]
fn f2(p: Option<(i32, i32)>) {
    f1(p)
}
