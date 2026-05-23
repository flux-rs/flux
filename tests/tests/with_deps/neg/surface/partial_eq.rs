extern crate flux_alloc;
use flux_rs::assert;

#[derive(Debug, Clone, PartialEq, Eq)]
struct Juror {
    name: String,
    age: u32,
}

fn test() {
    let juror1 = Juror { name: "Alice".to_string(), age: 30 };
    let juror2 = Juror { name: "Alice".to_string(), age: 30 };

    assert(juror1 == juror2); //~ ERROR refinement type
    assert(juror1 != juror2); //~ ERROR refinement type
}
