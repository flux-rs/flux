#![allow(dead_code)]

pub struct Cow {}

pub trait CowContainer<'apple> {
    fn get_cow(&self) -> &'apple Cow;
}

pub struct CowCell<'banana> {
    inner: &'banana dyn CowContainer<'banana>,
}
