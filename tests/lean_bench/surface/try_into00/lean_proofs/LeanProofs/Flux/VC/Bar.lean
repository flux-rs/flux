import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Bar := 
 ∀ (n₀ : Int),
  (42 = n₀) ->
   ((n₀ = 42) = True)
end F
