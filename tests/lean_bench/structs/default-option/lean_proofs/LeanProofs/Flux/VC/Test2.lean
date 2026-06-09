import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test2 := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> Prop, 
 (((k0 12))) ∧
 (∀ (a'₀ : Int),
  ((k0 a'₀)) ->
   ((k1 a'₀))) ∧
 (∀ (a'₁ : Int),
  ((k1 a'₁)) ->
   (10 ≤ a'₁))
 
end F
