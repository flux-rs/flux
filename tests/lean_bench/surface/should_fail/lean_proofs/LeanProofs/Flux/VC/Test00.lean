import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test00 := ¬
 ∀ (x₀ : Int),
  ((x₀ + 2) = (x₀ + 1))
end F
