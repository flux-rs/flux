use core::{marker::PhantomData, mem::MaybeUninit};

use flux_attrs::*;

#[opaque]
#[refined_by(len: int)]
#[repr(transparent)]
pub struct FluxSlice<T>([T]);

#[refined_by(ring: FluxSlice<MaybeUninit<T>>)] //~ ERROR sorts associated with this struct should have no generic arguments
pub struct RingBuffer<T>(PhantomData<T>);
