import ImplTrait.ImplTrait01.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Lib := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (x₀ : Int),
  (((k0 x₀ x₀))) ∧
  (∀ (a'₀ : Int),
   ((k0 a'₀ x₀)) ->
    ((k1 a'₀ x₀))) ∧
  (∀ (a'₁ : Int),
   ((k1 a'₁ x₀)) ->
    (x₀ ≤ a'₁))
  
end F
