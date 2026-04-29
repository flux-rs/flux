import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def I64U32Bounded := 
 ∀ (x₀ : Int),
  ((0 ≤ x₀) ∧ (x₀ ≤ 4294967295)) ->
   ∀ (a'₀ : Int),
    (a'₀ ≥ 0) ->
     ((x₀ ≥ 0) -> (a'₀ = x₀)) ->
      (a'₀ = x₀)
end F
