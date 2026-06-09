import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TrivialGe := 
 ∀ (x₀ : BitVec 32),
  ((BitVec.ule x₀ x₀) = (BitVec_uge x₀ x₀))
end F
