import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Slice := 
 ∀ (a'₀ : Int),
  (a'₀ ≥ 0) ->
   ∀ (v₀ : Int),
    (v₀ > 0) ->
     (v₀ ≥ 0)
end F
