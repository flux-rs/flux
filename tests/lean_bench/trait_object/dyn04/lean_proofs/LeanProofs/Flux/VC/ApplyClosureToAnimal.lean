import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def ApplyClosureToAnimal := 
 ∀ (c0 : Prop),
  ∀ (closure₀ : Int),
   False ->
    ((c0) ∨ False)
end F
