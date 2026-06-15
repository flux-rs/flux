pub trait Queue<T> {
    #[flux_rs::sig(fn(self: &strg Self, _) -> bool ensures self: Self)]
    fn enqueue(&mut self, val: T) -> bool;
}

#[flux_rs::refined_by(ring_len: int)]
pub struct RingBuffer<'a, T: 'a> {
    #[field(&mut [T][ring_len])]
    ring: &'a mut [T],
}

impl<T: Copy> Queue<T> for RingBuffer<'_, T> {
    #[flux_rs::sig(fn(self: &strg Self, _) -> bool ensures self: Self)]
    fn enqueue(&mut self, val: T) -> bool {
        true
    }
}
