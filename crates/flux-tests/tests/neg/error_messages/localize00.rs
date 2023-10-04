// ------ Test 1 -------------------------------------------------

#[flux::sig(fn(i32{v: 10 <= v && v <= 20}))] //~ NOTE this is the condition
pub fn pre(_n: i32) {}

pub fn test(n: i32) {
    if n < 15 {
        pre(n); //~ ERROR refinement type
                //~| NOTE a precondition cannot be proved
    }
}

// ------ Test 2 -------------------------------------------------

#[flux::sig(fn(n:i32, m:i32[n + 10]))] //~ NOTE this is the condition
pub fn pre2(_n: i32, _m: i32) {}

pub fn test2(n: i32) {
    pre2(n, n + n); //~ ERROR refinement type
                    //~| NOTE a precondition cannot be proved
}

// ------ Test 3 -------------------------------------------------

#[flux::sig(fn(n:i32{0 <= n}) -> i32{v: 100 <= v && v <= 200})] //~ NOTE this is the condition
pub fn post(n: i32) -> i32 {
    n + 100 //~ ERROR refinement type
            //~| NOTE a postcondition cannot be proved
}

// ------ Test 4 -------------------------------------------------
#[flux::sig(fn (n:i32{0 < n && n < 400}))] //~ NOTE this is the condition
pub fn floo(_n: i32) {}

pub fn test_floo() {
    floo(1000); //~ ERROR refinement type
                //~| NOTE a precondition cannot be proved
}
