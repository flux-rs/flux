extern crate flux_alloc;
use flux_alloc::string::mk_string;
use flux_rs::assert;

pub fn test_string() {
    let bob1 = mk_string("bob");
    let bob2 = mk_string("bob");
    let alice1 = mk_string("alice");
    assert(bob1 == bob1);
    assert(bob1 == bob2);
    assert(alice1 == alice1);
    assert(bob1 != alice1);
    assert(bob2 != alice1);
}
