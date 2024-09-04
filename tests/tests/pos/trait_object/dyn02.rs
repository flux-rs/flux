pub trait Animal {
    fn noise(&self);
}

#[flux::trusted]
pub fn get_animal() -> &'static dyn Animal {
    unimplemented!()
}
