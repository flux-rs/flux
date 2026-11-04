extern crate flux_core;

pub struct MyIter;

impl Iterator for MyIter {
    type Item = u32;

    fn next(&mut self) -> Option<u32> { //~ ERROR refinement type error
                                        //~| ERROR refinement type error
        None
    }
}
