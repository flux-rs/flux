import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> Prop, ∃ k2 : (a0 : Int) -> Prop, ∃ k3 : (a0 : Int) -> Prop, ∃ k4 : (a0 : Int) -> (a1 : Int) -> Prop, 
 (((k0 0))) ∧
 (∀ (a'₀ : Int),
  ((k1 a'₀)) ->
   ((k0 a'₀))) ∧
 (∀ (a'₁ : Int),
  ((k0 a'₁)) ->
   ((k1 a'₁))) ∧
 (((k2 1))) ∧
 (∀ (a'₂ : Int),
  ((k0 a'₂)) ->
   ((k2 a'₂))) ∧
 (∀ (a'₃ : Int),
  ((k2 a'₃)) ->
   ((k0 a'₃))) ∧
 ((0 < ((0 + 1) + 1))) ∧
 (∀ (a'₄ : Int),
  ((k2 a'₄)) ->
   ((k3 a'₄))) ∧
 (∀ (a'₅ : Int),
  ((k3 a'₅)) ->
   ((k2 a'₅))) ∧
 (∀ (a'₆ : Int),
  ((k3 a'₆)) ->
   (((k3 (a'₆ + 1)))) ∧
   ((1 < ((0 + 1) + 1))) ∧
   (∀ (a'₇ : Int),
    ((k3 a'₇)) ->
     ((k4 a'₇ a'₆))) ∧
   (∀ (a'₈ : Int),
    ((k4 a'₈ a'₆)) ->
     ((k3 a'₈))) ∧
   (∀ (a'₉ : Int),
    ((k4 a'₉ a'₆)) ->
     (a'₉ ≥ 0))
   )
 
end F
