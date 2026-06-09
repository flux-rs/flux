import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Div := 
 ∀ (x₀ : Int),
  (x₀ > 0) ->
   ((x₀ ≠ 0)) ∧
   ((x₀ ≠ 0) ->
    ∀ (a'₀ : Int),
     ((x₀ ≥ 0) -> (a'₀ = (1 / x₀))) ->
      (a'₀ = (1 / x₀)))
   
end F
