import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Inc := 
 ∀ (x₀ : Int),
  ∀ (y₀ : Int),
   (¬(x₀ < y₀)) ->
    (x₀ < (x₀ + 1))
end F
