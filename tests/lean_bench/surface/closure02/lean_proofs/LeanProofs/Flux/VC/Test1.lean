import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test1 := ∃ k0 : (a0 : Prop) -> Prop, ∃ k1 : (a0 : Prop) -> Prop, 
 (∀ (a'₀ : Prop),
  ((k0 a'₀)) ->
   a'₀ ->
    (10 ≤ (6 + 10))) ∧
 (∀ (a'₁ : Prop),
  ((k1 a'₁)) ->
   ((k0 a'₁))) ∧
 (∀ (a'₂ : Prop),
  ((k1 a'₂)))
 
end F
