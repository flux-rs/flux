import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestAndA := 
 ∀ (x₀ : BitVec 8),
  (x₀ = 6#8) ->
   ((BitVec.and x₀ 3#8) = 2#8)
end F
