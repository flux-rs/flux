import Enums.List00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Empty := 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   ∀ (n₁ : Int),
    (n₀ = (n₁ + 1)) ->
     ∀ (a'₁ : Int),
      (n₁ ≥ 0) ->
       (False = (n₀ = 0))
end F
