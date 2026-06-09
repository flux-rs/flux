import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test := 
 ∀ (ptr₀ : Int),
  ∀ (ptr₁ : Int),
   (ptr₁ ≥ ptr₀) ->
    ((((ptr₁ + 0) ≥ ptr₀)) ∧
    (((2 - 0) > 0))
    ) ∧
    ((((ptr₁ + 1) ≥ ptr₀)) ∧
    (((2 - 1) > 0))
    )
    
end F
