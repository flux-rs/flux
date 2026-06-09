import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestAndNoneLeft := 
 ∀ (x₀ : Prop),
  ((x₀ = x₀) = True)
end F
