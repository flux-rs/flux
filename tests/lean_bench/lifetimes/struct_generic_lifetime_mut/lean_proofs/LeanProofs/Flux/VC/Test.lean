import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test := 
 ∀ (x₀ : Int),
  (x₀ ≥ 0) ->
   (((x₀ + 1) > 0)) ∧
   (∀ (v₀ : Int),
    (v₀ > 0) ->
     ((v₀ + 1) > 0))
   
end F
