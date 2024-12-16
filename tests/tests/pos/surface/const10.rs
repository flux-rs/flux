pub struct Cow {}

const GRASS: usize = 12;
impl Cow {
    #[flux_rs::sig(fn () -> usize[12])]
    fn test() -> usize {
        GRASS
    }
}
