import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestSkipSlice := 
 ∀ (n₀ : Int),
  (n₀ ≥ 2) ->
   (n₀ ≥ 0) ->
    ∀ (v₀ : Int),
     (v₀ = (if (0 > ((n₀ - 0) - 2)) then 0 else ((n₀ - 0) - 2))) ->
      (0 ≤ v₀) ->
       (v₀ = (n₀ - 2))
end F
