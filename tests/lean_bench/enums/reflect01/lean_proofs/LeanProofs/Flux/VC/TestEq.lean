import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Struct.State
open Classical
set_option linter.unusedVariables false


namespace F



def TestEq := 
 ((((State.mkState₀) = (State.mkState₀)) = True)) ∧
 ((((State.mkState₀) = (State.mkState₀)) = True)) ∧
 (∀ (v₀ : Prop),
  (v₀ <-> ((State.mkState₀) ≠ (State.mkState₁))) ->
   (v₀ = True))
 
end F
