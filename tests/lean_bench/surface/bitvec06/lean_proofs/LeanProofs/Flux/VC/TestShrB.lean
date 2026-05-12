import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestShrB := 
 ∀ (x₀ : BitVec 8),
  (x₀ = 4#8) ->
   ((BitVec_ushiftRight x₀ 2#8) = 1#8)
end F
