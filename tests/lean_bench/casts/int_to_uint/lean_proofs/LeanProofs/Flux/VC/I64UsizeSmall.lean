import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def I64UsizeSmall := 
 ∀ (x₀ : Int),
  ((0 ≤ x₀) ∧ (x₀ ≤ 100)) ->
   ∀ (a'₀ : Int),
    (a'₀ ≥ 0) ->
     ((x₀ ≥ 0) -> (a'₀ = x₀)) ->
      (a'₀ ≤ 100)
end F
