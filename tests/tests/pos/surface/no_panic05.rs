#![feature(stmt_expr_attributes)]

fn okay_if_i_panic() {
    let bad_thing = |x: i32| { panic!("this is ok"); x };
    bad_thing(1);
}

#[flux::no_panic]
fn i_cant_panic() {
    let good_thing = |x: i32| { 
        {
            x
        }
    };
    good_thing(1);
}

#[flux::no_panic]
fn main() {
    let x = 12;
}
