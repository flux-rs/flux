import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test4 := 
 ∀ (v₀ : Int),
  (0 ≤ v₀) ->
   (0 ≤ (v₀ + 1))
end F
