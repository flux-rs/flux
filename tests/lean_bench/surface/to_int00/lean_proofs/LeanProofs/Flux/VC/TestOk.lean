import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestOk := 
 ∀ (x₀ : Int),
  (x₀ ≤ 1114111) ->
   (0 ≤ x₀) ->
    (let a'₁ := x₀; ((48 ≤ a'₁) ∧ (a'₁ ≤ 57))) ->
     ((let a'₂ := x₀; ((0 ≤ a'₂) ∧ (a'₂ ≤ 127))) = True)
end F
