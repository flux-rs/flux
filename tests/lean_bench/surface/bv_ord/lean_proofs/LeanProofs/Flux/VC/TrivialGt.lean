import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TrivialGt := 
 ∀ (x₀ : BitVec 32),
  ((BitVec.ult x₀ x₀) = (BitVec_ugt x₀ x₀))
end F
