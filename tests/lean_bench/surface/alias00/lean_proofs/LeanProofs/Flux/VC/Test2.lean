import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test2 := 
 ∀ (v₀ : Int),
  (10 ≤ v₀) ->
   (10 ≤ (v₀ + 1))
end F
