import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestDigit := 
 ∀ (v₀ : Int),
  ((48 ≤ v₀) ∧ (v₀ ≤ 57)) ->
   (v₀ ≤ 1114111) ->
    (0 ≤ v₀) ->
     ((let a'₁ := v₀; ((48 ≤ a'₁) ∧ (a'₁ ≤ 57))) = True)
end F
