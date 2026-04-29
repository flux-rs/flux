import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def I32U8LosslessReft := 
 ∀ (n₀ : Int),
  ((0 ≤ n₀) ∧ (n₀ < 12)) ->
   ∀ (a'₀ : Int),
    (a'₀ ≥ 0) ->
     (((n₀ ≥ 0) ∧ (n₀ ≤ 255)) -> (a'₀ = n₀)) ->
      (a'₀ < 12)
end F
