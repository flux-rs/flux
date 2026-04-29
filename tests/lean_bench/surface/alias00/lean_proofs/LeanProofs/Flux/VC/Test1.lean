import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test1 := 
 ∀ (n₀ : Int),
  (0 ≤ n₀) ->
   (0 ≤ (n₀ + 1))
end F
