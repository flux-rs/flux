import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def RequiresNegative := 
 ∀ (x₀ : Int),
  (((x₀ + 1) = (1 + x₀)) = True)
end F
