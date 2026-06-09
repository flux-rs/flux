import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Len := 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   ((n₀ = 0) ->
    (0 = n₀)) ∧
   (∀ (n₁ : Int),
    (n₀ = (n₁ + 1)) ->
     ∀ (a'₁ : Int),
      (n₁ ≥ 0) ->
       ((1 + n₁) = n₀))
   
end F
