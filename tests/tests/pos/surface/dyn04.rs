pub trait Animal {
    fn noise(&self);
}

pub fn apply_closure_to_animal<F>(closure: F, animal: &'static dyn Animal)
where
    F: FnOnce(&dyn Animal),
{
    closure(animal);
}
