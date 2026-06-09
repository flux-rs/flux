import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Burpi := ∃ k0 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 ∀ (k₀ : Int),
  ∀ (a'₀ : Int),
   ((k₀ ≥ 0) -> (a'₀ = (k₀ % 2))) ->
    (¬(a'₀ ≠ 0)) ->
     (((k0 (k₀ + 1) k₀ a'₀))) ∧
     (∀ (a'₁ : Int),
      ((k0 a'₁ k₀ a'₀)) ->
       (k₀ < a'₁))
     
end F
