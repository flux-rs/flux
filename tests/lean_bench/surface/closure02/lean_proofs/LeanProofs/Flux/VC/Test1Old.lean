import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test1Old := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, ∃ k2 : (a0 : Int) -> Prop, ∃ k3 : (a0 : Int) -> Prop, ∃ k4 : (a0 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  ∀ (a'₁ : Int),
   ((k0 a'₀ a'₁)) ->
    ((k1 (a'₀ + a'₁) a'₀ a'₁))) ∧
 (∀ (a'₂ : Int),
  ((k2 a'₂)) ->
   ∀ (a'₃ : Int),
    ((k3 a'₃)) ->
     (((k0 a'₂ a'₃))) ∧
     (∀ (a'₄ : Int),
      ((k1 a'₄ a'₂ a'₃)) ->
       ((k4 a'₄)))
     ) ∧
 (((k2 3))) ∧
 (∀ (v₀ : Int),
  (0 ≤ v₀) ->
   ((k3 v₀))) ∧
 (∀ (a'₆ : Int),
  ((k4 a'₆)) ->
   (3 ≤ a'₆))
 
end F
