#[repr(u32)]
pub enum SyscallReturnVariant {
    Failure = 0,
}

pub struct MLFQSched<'a> {
    pub processes: &'a [i32; 3],
}

impl<'a> MLFQSched<'a> {
    pub const NUM_QUEUES: usize = 3;

    pub fn test(&self, queue_idx: usize) -> i32 {
        let next_queue = if queue_idx == Self::NUM_QUEUES - 1 { queue_idx } else { queue_idx + 1 };
        123
    }
}
