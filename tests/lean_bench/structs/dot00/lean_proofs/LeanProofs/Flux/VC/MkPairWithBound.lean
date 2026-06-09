import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def MkPairWithBound := 
 ∀ (a₀ : Int),
  ((a₀ + 0) ≤ a₀)
end F
