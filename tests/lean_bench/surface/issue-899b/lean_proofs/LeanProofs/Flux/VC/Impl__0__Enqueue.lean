import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.RingBuffer
import LeanFixpoint
open Classical

namespace F



def Impl__0__Enqueue := 
 ∀ (a'₀ : RingBuffer),
  ∀ (a'₁ : Int),
   ((RingBuffer.ring_len a'₀) > 1) ->
    ∀ (a'₂ : Prop),
     (¬a'₂) ->
      ((RingBuffer.ring_len a'₀) ≥ 0) ->
       ((RingBuffer.hd a'₀) < (RingBuffer.ring_len a'₀)) ->
        ((RingBuffer.hd a'₀) ≥ 0) ->
         ((RingBuffer.tl a'₀) < (RingBuffer.ring_len a'₀)) ->
          ((RingBuffer.tl a'₀) ≥ 0) ->
           (((RingBuffer.ring_len a'₀) ≠ 0)) ∧
           (((RingBuffer.ring_len a'₀) ≠ 0) ->
            ((((RingBuffer.tl a'₀) + 1) % (RingBuffer.ring_len a'₀)) < (RingBuffer.ring_len a'₀)))
           
end F
