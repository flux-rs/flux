import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestMapSlice := 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   ∀ (v₀ : Int),
    (v₀ = (n₀ - 0)) ->
     (0 ≤ v₀) ->
      (v₀ = n₀)
end F
