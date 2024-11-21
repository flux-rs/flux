use core::slice::{Iter, SliceIndex};

pub trait Queue<T> {
    /// Returns true if the queue is full, false otherwise.
    fn is_full(&self) -> bool;

    /// If the queue isn't full, add a new element to the back of the queue.
    /// Returns whether the element was added.
    #[flux_rs::sig(fn(self: &strg Self, _) -> bool ensures self: Self)]
    fn enqueue(&mut self, val: T) -> bool;
}


#[flux_rs::extern_spec]
impl<T> [T] {
    #[flux_rs::sig(fn(&[T][@len]) -> usize[len])]
    fn len(v: &[T]) -> usize;
}


#[flux_rs::refined_by(ring_len: int, hd: int, tl: int)]
#[flux_rs::invariant(ring_len > 1)]
pub struct RingBuffer<'a, T: 'a> {
    #[field({&mut [T][ring_len] | ring_len > 1})]
    ring: &'a mut [T],
    #[field({usize[hd] | hd < ring_len})]
    head: usize,
    #[field({usize[tl] | tl < ring_len})]
    tail: usize,
}

impl<T: Copy> Queue<T> for RingBuffer<'_, T> {
    fn is_full(&self) -> bool {
        self.head == ((self.tail + 1) % self.ring.len())
    }

    #[flux_rs::sig(fn(self: &strg Self, _) -> bool ensures self: Self)]
    fn enqueue(&mut self, val: T) -> bool {
        if self.is_full() {
            // Incrementing tail will overwrite head
            false
        } else {
            self.ring[self.tail] = val;
            self.tail = (self.tail + 1) % self.ring.len();
            true
        }
    }
