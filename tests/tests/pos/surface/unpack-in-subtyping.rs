//@ignore-test: we used to accept this but now since all generic types are of kind base
// it is not longer well-formed. If we accept variables of kind base we could try to accept
// this again

#[flux::sig(fn(Option<{a. (i32[a], {b. {i32[b] | a > b}})}>))]
fn f1(p: Option<(i32, i32)>) {
    f2(p)
}

#[flux::sig(fn(Option<{a,b:int. ({i32[a] | b < a}, i32[b])}>))]
fn f2(p: Option<(i32, i32)>) {
    f1(p)
}
