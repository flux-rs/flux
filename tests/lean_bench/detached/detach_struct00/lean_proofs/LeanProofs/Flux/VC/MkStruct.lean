import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def MkStruct := 
 ∀ (x₀ : Int),
  ∀ (y₀ : Int),
   (x₀ ≥ 0) ->
    (y₀ ≥ 0) ->
     ((¬(x₀ < y₀)) ->
      (y₀ ≤ x₀)) ∧
     ((x₀ < y₀) ->
      (x₀ ≤ y₀))
     
end F
