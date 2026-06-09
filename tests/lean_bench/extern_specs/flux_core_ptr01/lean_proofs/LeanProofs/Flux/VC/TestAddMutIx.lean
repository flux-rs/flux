import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestAddMutIx := 
 ∀ (base₀ : Int),
  ∀ (addr₀ : Int),
   ∀ (size₀ : Int),
    ((addr₀ ≥ base₀) ∧ (size₀ = 2)) ->
     ((((addr₀ + 0) ≥ base₀)) ∧
     (((size₀ - 0) > 0))
     ) ∧
     ((((addr₀ + 1) ≥ base₀)) ∧
     (((size₀ - 1) > 0))
     )
     
end F
