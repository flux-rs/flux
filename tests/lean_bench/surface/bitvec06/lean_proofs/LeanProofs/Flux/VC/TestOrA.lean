import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestOrA := 
 ∀ (x₀ : BitVec 8),
  (x₀ = 4#8) ->
   ((BitVec.or x₀ 1#8) = 5#8)
end F
