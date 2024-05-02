#![flux::ignore] // default to ignore for the entire crate

#[flux::ignore(no)] // include this module
mod included {
    #[flux::sig(fn(bool[true]))]
    pub fn assert(_: bool) {}

    pub fn test1() {
        // we are indeed checking this code
        assert(20 < 10); //~ ERROR refinement type error
    }

    pub fn test2() {
        // we cannot use an ignored function in included code
        crate::ignored_fun(); //~ERROR use of ignored function
    }
}

// bad refinement, but no error since we are ignoring this function
#[flux::sig(fn(i32, i32))]
pub fn malformed(_: i32) {}

// an ignored function that cannot be used in included code
pub fn ignored_fun() {}
