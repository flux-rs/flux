import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def WriteIxI32 := 
 ∀ (base₀ : Int),
  ∀ (addr₀ : Int),
   ∀ (size₀ : Int),
    ∀ (value₀ : Int),
     ((addr₀ ≥ base₀) ∧ (size₀ = 99)) ->
      (size₀ > 0)
end F
