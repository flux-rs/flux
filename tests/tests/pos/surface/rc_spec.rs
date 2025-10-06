extern crate flux_alloc;
use std::rc::Rc;

use flux_alloc::string::mk_string;
use flux_rs::assert;

pub fn test_rc() {
    let bob1 = mk_string("bob");
    let rc_bob = Rc::new(bob1);
    let bob2 = mk_string("bob"); // bob1.clone();
    assert(bob2 == *rc_bob);
}
