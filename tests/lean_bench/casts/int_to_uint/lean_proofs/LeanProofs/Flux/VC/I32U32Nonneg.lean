import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def I32U32Nonneg := 
 ∀ (x₀ : Int),
  (0 ≤ x₀) ->
   ∀ (a'₀ : Int),
    (a'₀ ≥ 0) ->
     ((x₀ ≥ 0) -> (a'₀ = x₀)) ->
      (a'₀ = x₀)
end F
