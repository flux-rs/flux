import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestShlB := 
 ∀ (x₀ : BitVec 8),
  (x₀ = 1#8) ->
   ((BitVec_shiftLeft x₀ 2#8) = 4#8)
end F
