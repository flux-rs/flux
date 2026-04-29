import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def RefParam := 
 ∀ (v₀ : Int),
  (0 ≤ v₀) ->
   (((v₀ + 1) > 0) = True)
end F
