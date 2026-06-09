import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Apply := 
 ∀ (c0 : Prop),
  ∀ (f₀ : Int),
   ∀ (x₀ : Int),
    False ->
     ((c0) ∨ False)
end F
