import Surface.Async01.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def MakeNat := 
 ∀ (n₀ : Int),
  (n₀ ≤ (n₀ + 1))
end F
