import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F

@[ext]
structure RingBuffer  where
  mkRingBuffer₀ ::
    ring_len : Int 
    hd : Int 
    tl : Int 


end F
