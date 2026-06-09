import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def BobInc := 
 ∀ (n₀ : Int),
  (n₀ < (n₀ + 1))
end F
