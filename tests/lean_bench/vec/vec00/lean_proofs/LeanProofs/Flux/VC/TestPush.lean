import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestPush := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> Prop, ∃ k2 : (a0 : Int) -> Prop, ∃ k3 : (a0 : Int) -> Prop, ∃ k4 : (a0 : Int) -> Prop, 
 (((k0 10))) ∧
 ((0 ≤ (0 + 1)) ->
  (∀ (a'₀ : Int),
   ((k0 a'₀)) ->
    ((k1 a'₀))) ∧
  (((k1 20))) ∧
  ((0 ≤ ((0 + 1) + 1)) ->
   (∀ (a'₁ : Int),
    ((k1 a'₁)) ->
     ((k2 a'₁))) ∧
   (((k2 30))) ∧
   ((0 ≤ (((0 + 1) + 1) + 1)) ->
    (∀ (a'₂ : Int),
     ((k2 a'₂)) ->
      ((k3 a'₂))) ∧
    ((0 ≤ (if ((((0 + 1) + 1) + 1) > 0) then ((((0 + 1) + 1) + 1) - 1) else 0)) ->
     (∀ (a'₃ : Int),
      ((k3 a'₃)) ->
       ((k4 a'₃))) ∧
     ((((((0 + 1) + 1) + 1) > 0) = True)) ∧
     (∀ (val₀ : Int),
      ((k4 val₀)) ->
       (((val₀ ≥ 10) = True)) ∧
       (((if ((((0 + 1) + 1) + 1) > 0) then ((((0 + 1) + 1) + 1) - 1) else 0) = 2))
       )
     )
    )
   )
  )
 
end F
