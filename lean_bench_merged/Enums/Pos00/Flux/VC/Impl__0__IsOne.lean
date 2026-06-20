import Enums.Pos00.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Impl__0__IsOne := 
 ∀ (n₀ : Int),
  (n₀ > 0) ->
   (∀ (n₁ : Int),
    (n₀ = (2 * n₁)) ->
     (n₁ > 0) ->
      (False = (n₀ = 1))) ∧
   (∀ (n₂ : Int),
    (n₀ = ((2 * n₂) + 1)) ->
     (n₂ > 0) ->
      (False = (n₀ = 1)))
   
end F
