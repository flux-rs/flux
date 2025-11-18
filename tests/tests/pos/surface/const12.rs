// Test that we can check a generic associated constant in the mir

trait Trait {
    const C: usize;
}

fn test<T: Trait>() -> usize {
    T::C
}
