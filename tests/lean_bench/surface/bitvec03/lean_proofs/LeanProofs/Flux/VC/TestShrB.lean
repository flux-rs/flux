import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestShrB := 
 ∀ (x₀ : BitVec 32),
  (x₀ = 8#32) ->
   ((BitVec_ushiftRight x₀ 3#32) = 1#32)
end F
