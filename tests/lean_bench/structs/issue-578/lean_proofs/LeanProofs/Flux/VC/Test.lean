import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> Prop, ∃ k2 : (a0 : Int) -> Prop, ∃ k3 : (a0 : Int) -> Prop, ∃ k4 : (a0 : Int) -> Prop, ∃ k5 : (a0 : Int) -> Prop, 
 (((k0 0))) ∧
 (∀ (a'₀ : Int),
  ((k0 a'₀)) ->
   ((k1 a'₀))) ∧
 (((k1 1))) ∧
 (∀ (a'₁ : Int),
  ((k1 a'₁)) ->
   ((k2 a'₁))) ∧
 (∀ (a'₂ : Int),
  (a'₂ = 0) ->
   (k3 a'₂)) ∧
 (∀ (a'₃ : Int),
  ((k2 a'₃)) ->
   ((k4 a'₃))) ∧
 (∀ (a'₄ : Int),
  (a'₄ = 0) ->
   (k3 a'₄) ->
    (∀ (a'₅ : Int),
     ((k4 a'₅)) ->
      ((k5 a'₅))) ∧
    (∀ (a'₆ : Int),
     ((k5 a'₆)) ->
      (((a'₆ ≥ 0) = True)) ∧
      (∀ (a'₇ : Int),
       ((k5 a'₇)) ->
        ((k4 a'₇)))
      )
    )
 
end F
