import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def CloseAtReturn := ∃ k0 : (a0 : Int) -> Prop, 
 (((k0 1))) ∧
 (∀ (x₀ : Int),
  ((k0 x₀)) ->
   ((x₀ + 1) = 2))
 
end F
