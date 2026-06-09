import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test3 := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> Prop, ∃ k2 : (a0 : Int) -> Prop, 
 (((k0 0))) ∧
 ((0 ≤ (0 + 1)) ->
  (∀ (a'₀ : Int),
   ((k0 a'₀)) ->
    ((k1 a'₀))) ∧
  (((k1 1))) ∧
  ((0 ≤ ((0 + 1) + 1)) ->
   ((0 < ((0 + 1) + 1))) ∧
   (∀ (a'₁ : Int),
    ((k1 a'₁)) ->
     ((k2 a'₁))) ∧
   (∀ (a'₂ : Int),
    ((k2 a'₂)) ->
     (a'₂ ≥ 0) ->
      (1 < ((0 + 1) + 1)))
   )
  )
 
end F
