import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#2}MIN
import LeanProofs.Flux.Fun.Num{impl#2}MAX
import LeanFixpoint
open Classical

namespace F



def TestBothBoundedConcrete := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k2 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k3 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> (a3 : Int) -> Prop, 
 ((((num_{impl#2}_MIN ≤ 42) ∧ (42 ≤ num_{impl#2}_MAX)) = True)) ∧
 (∀ (a'₀ : Int),
  (a'₀ = 42) ->
   ((k0 a'₀))) ∧
 ((((num_{impl#2}_MIN ≤ 42) ∧ (42 ≤ num_{impl#2}_MAX)) = True)) ∧
 (∀ (a'₁ : Int),
  ((k0 a'₁)) ->
   (((a'₁ = 42) = True)) ∧
   (∀ (a'₂ : Int),
    (a'₂ = (-42)) ->
     ((k1 a'₂ a'₁))) ∧
   ((((num_{impl#2}_MIN ≤ (-42)) ∧ ((-42) ≤ num_{impl#2}_MAX)) = True)) ∧
   (∀ (a'₃ : Int),
    ((k1 a'₃ a'₁)) ->
     (((a'₃ = (-42)) = True)) ∧
     (∀ (a'₄ : Int),
      (a'₄ = 2147483647) ->
       ((k2 a'₄ a'₁ a'₃))) ∧
     ((((num_{impl#2}_MIN ≤ 2147483647) ∧ (2147483647 ≤ num_{impl#2}_MAX)) = True)) ∧
     (∀ (a'₅ : Int),
      ((k2 a'₅ a'₁ a'₃)) ->
       (((a'₅ = 2147483647) = True)) ∧
       (∀ (a'₆ : Int),
        (a'₆ = (-2147483648)) ->
         ((k3 a'₆ a'₁ a'₃ a'₅))) ∧
       ((((num_{impl#2}_MIN ≤ (-2147483648)) ∧ ((-2147483648) ≤ num_{impl#2}_MAX)) = True)) ∧
       (∀ (a'₇ : Int),
        ((k3 a'₇ a'₁ a'₃ a'₅)) ->
         (((a'₇ = (-2147483648)) = True)) ∧
         (((¬((num_{impl#2}_MIN ≤ (2147483647 + 1)) ∧ ((2147483647 + 1) ≤ num_{impl#2}_MAX))) = True)) ∧
         (((¬((num_{impl#2}_MIN ≤ ((-2147483648) - 1)) ∧ (((-2147483648) - 1) ≤ num_{impl#2}_MAX))) = True))
         )
       )
     )
   )
 
end F
