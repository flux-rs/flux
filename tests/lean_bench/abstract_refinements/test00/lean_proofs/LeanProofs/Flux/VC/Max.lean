import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Max := 
 ∀ (p₀ : (Int -> Prop)),
  ∀ (x₀ : Int),
   ∀ (y₀ : Int),
    ((p₀ x₀) ∧ (p₀ y₀)) ->
     ((¬(x₀ > y₀)) ->
      ((y₀ ≥ x₀)) ∧
      ((y₀ ≥ y₀))
      ) ∧
     ((x₀ > y₀) ->
      ((x₀ ≥ x₀)) ∧
      ((x₀ ≥ y₀))
      )
     
end F
