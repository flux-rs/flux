import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test002Client := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> (a2 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  ∀ (a'₁ : Int),
   ((k0 a'₀ a'₁)) ->
    ((k1 ((a'₀ + a'₁) + 10) a'₀ a'₁))) ∧
 (∀ (v₀ : Int),
  (0 ≤ v₀) ->
   ∀ (v₁ : Int),
    (0 ≤ v₁) ->
     (((k0 v₀ v₁))) ∧
     (∀ (a'₄ : Int),
      ((k1 a'₄ v₀ v₁)) ->
       (10 ≤ a'₄))
     )
 
end F
