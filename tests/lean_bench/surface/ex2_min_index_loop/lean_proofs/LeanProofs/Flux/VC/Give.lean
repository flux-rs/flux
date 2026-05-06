import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Give := 
 ∀ (n₀ : Int),
  (n₀ > 0) ->
   (0 ≤ n₀) ->
    (0 < n₀)
end F
