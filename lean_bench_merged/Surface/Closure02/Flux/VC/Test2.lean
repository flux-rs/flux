import Surface.Closure02.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test2 := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> Prop, ∃ k2 : (a0 : Int) -> Prop, ∃ k3 : (a0 : Prop) -> Prop, ∃ k4 : (a0 : Prop) -> Prop, 
 (((k0 100))) ∧
 ((0 ≤ (0 + 1)) ->
  (∀ (a'₀ : Int),
   ((k0 a'₀)) ->
    ((k1 a'₀))) ∧
  (((k1 200))) ∧
  ((0 ≤ ((0 + 1) + 1)) ->
   (∀ (a'₁ : Int),
    ((k1 a'₁)) ->
     ((k2 a'₁))) ∧
   (((k2 300))) ∧
   ((0 ≤ (((0 + 1) + 1) + 1)) ->
    (∀ (a'₂ : Prop),
     ((k3 a'₂)) ->
      a'₂ ->
       ((0 < (((0 + 1) + 1) + 1))) ∧
       (∀ (a'₃ : Int),
        ((k2 a'₃)) ->
         (10 ≤ a'₃))
       ) ∧
    (∀ (a'₄ : Prop),
     ((k4 a'₄)) ->
      ((k3 a'₄))) ∧
    (∀ (a'₅ : Prop),
     ((k4 a'₅)))
    )
   )
  )
 
end F
