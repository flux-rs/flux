import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test1 := 
 ∀ (n₀ : Int),
  (0 ≤ n₀) ->
   (n₀ > 0) ->
    (0 < n₀)
end F
