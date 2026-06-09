import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Dec := 
 ∀ (x₀ : Int),
  ((x₀ - 1) < x₀)
end F
