import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestAndB := 
 ∀ (x₀ : BitVec 32),
  (x₀ = 10#32) ->
   ((BitVec.and x₀ 3#32) = 2#32)
end F
