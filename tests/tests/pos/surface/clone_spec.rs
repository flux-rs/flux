extern crate flux_alloc;
use flux_alloc::string::mk_string;
use flux_rs::assert;

// #[trusted]
// #[spec(fn(&str[@s]) -> String[s])]
// fn mk_string(s: &str) -> String {
//     s.to_string()
// }

pub fn test_clone() {
    let bob1 = mk_string("bob");
    let bob2 = bob1.clone();
    assert(bob1 == bob2);
}
