pub struct Person;

impl Person {
    const ID: i32 = 10;
}

#[flux::sig(fn() -> i32[10])]
pub fn test0() -> i32 {
    let id = Person::ID;
    id
}

#[flux::sig(fn() -> i32[11])]
pub fn test1() -> i32 {
    let id = Person::ID;
    id //~ ERROR refinement type
}
