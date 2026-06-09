import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test00 := ∃ k0 : (a0 : Int) -> Prop, 
 (((k0 1))) ∧
 (∀ (a'₀ : Int),
  ((k0 a'₀)) ->
   (a'₀ > 0))
 
end F
