import LeanProofs.Flux.Prelude
open Classical

namespace F

@[ext]
structure RingBuffer  where
  mkRingBuffer₀ ::
    ring_len : Int 
    hd : Int 
    tl : Int 


end F
