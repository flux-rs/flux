import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestOrB := 
 ∀ (x₀ : BitVec 32),
  (x₀ = 8#32) ->
   ((BitVec.or x₀ 3#32) = 11#32)
end F
