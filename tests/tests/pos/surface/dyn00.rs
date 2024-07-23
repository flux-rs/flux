#![allow(unused)]

trait Animal {
    fn noise(&self);
}

struct Cow {}

impl Animal for Cow {
    fn noise(&self) {
        println!("moooooo!");
    }
}

#[flux::trusted]
fn make_two_noises(animal: &dyn Animal) {
    animal.noise();
    animal.noise();
}

fn main() {
    let cow = Cow {};
    make_two_noises(&cow);
}
