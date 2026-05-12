import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestOrB := 
 ∀ (x₀ : BitVec 8),
  (x₀ = 4#8) ->
   ((BitVec.or x₀ 3#8) = 7#8)
end F
