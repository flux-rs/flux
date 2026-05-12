import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestShlA := 
 ∀ (x₀ : BitVec 8),
  (x₀ = 1#8) ->
   ((BitVec_shiftLeft x₀ 3#8) = 8#8)
end F
