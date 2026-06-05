#[flux::sig(fn(*const[@base, @addr] i32))] //~ ERROR this type takes 3 refinement arguments but 2 were found
pub fn const_too_few(_ptr: *const i32) {}

#[flux::sig(fn(*mut[@base, @addr] i32))] //~ ERROR this type takes 3 refinement arguments but 2 were found
pub fn mut_too_few(_ptr: *mut i32) {}

#[flux::sig(fn(*const[@base, @addr, @size, @extra] i32))] //~ ERROR this type takes 3 refinement arguments but 4 were found
pub fn const_too_many(_ptr: *const i32) {}

#[flux::sig(fn(*mut[@base, @addr, @size, @extra] i32))] //~ ERROR this type takes 3 refinement arguments but 4 were found
pub fn mut_too_many(_ptr: *mut i32) {}

#[flux::sig(fn({*const[@p] i32 | p.foo > 0}))] //~ ERROR no field `foo` on sort `ptr`
pub fn const_bad_field(_ptr: *const i32) {}

#[flux::sig(fn({*mut[@p] i32 | p.foo > 0}))] //~ ERROR no field `foo` on sort `ptr`
pub fn mut_bad_field(_ptr: *mut i32) {}

#[flux::sig(fn(*const{p: p.foo > 0} i32))] //~ ERROR no field `foo` on sort `ptr`
pub fn const_short_bad_field(_ptr: *const i32) {}

#[flux::sig(fn(*mut{p: p.foo > 0} i32))] //~ ERROR no field `foo` on sort `ptr`
pub fn mut_short_bad_field(_ptr: *mut i32) {}
