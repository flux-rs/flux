import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Exists := 
 ∀ (v₀ : Int),
  ((v₀ > 0) ∧ (v₀ < 10)) ->
   (((v₀ + 1) > 0)) ∧
   (((v₀ + 1) < 11))
   
end F
