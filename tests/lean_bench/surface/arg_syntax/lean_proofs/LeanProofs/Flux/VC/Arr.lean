import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Arr := 
 ∀ (v₀ : Int),
  (v₀ > 0) ->
   (v₀ ≥ 0)
end F
