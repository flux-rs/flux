import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test02 := ∃ k0 : (a0 : Prop) -> Prop, 
 (∀ (a'₀ : Int),
  ((k0 True))) ∧
 (∀ (a'₁ : Prop),
  ((k0 a'₁)) ->
   (a'₁ = True))
 
end F
