import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def SetSafeOffset := 
 ∀ (a'₀ : Int),
  (a'₀ ≥ 0) ->
   ∀ (a'₁ : Int),
    (a'₁ ≥ 0) ->
     (¬(a'₀ ≤ a'₁)) ->
      ((a'₀ - a'₁) ≥ 0)
end F
