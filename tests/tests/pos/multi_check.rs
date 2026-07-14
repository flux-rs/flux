//@compile-flags: -Fmulti-check=def:multi_check -Fdump-constraint=true

#[flux::sig(fn(i32[@x]) requires x != 0)]
fn check(x: i32) {}

#[flux::sig(fn(i32[@x]) requires x > 0)]
fn multi_check_1(x: i32) {
    check(x);
}

#[flux::sig(fn(i32[@x]) requires x > 2)]
fn multi_check_2(x: i32) {
    check(x);
}

fn multi_check(input: i32) {
    multi_check_1(input);
    multi_check_2(input);
}
