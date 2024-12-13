pub struct Cow {}

impl Cow {
    const GRASS: usize = 12;

    /// TODO: #[flux_rs::sig(fn () -> usize[12])]
    pub fn test() -> usize {
        Self::GRASS
    }
}
