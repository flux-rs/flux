import Surface.Closure02.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test2Old := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k2 : (a0 : Int) -> Prop, ∃ k3 : (a0 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  ((k0 a'₀)) ->
   ((k1 ((a'₀ + 1) + 2) a'₀))) ∧
 (∀ (a'₁ : Int),
  ((k2 a'₁)) ->
   (((k0 a'₁))) ∧
   (∀ (a'₂ : Int),
    ((k1 a'₂ a'₁)) ->
     ((k3 a'₂)))
   ) ∧
 (∀ (v₀ : Int),
  (0 ≤ v₀) ->
   ((k2 v₀))) ∧
 (∀ (a'₄ : Int),
  ((k3 a'₄)) ->
   (3 ≤ a'₄))
 
end F
