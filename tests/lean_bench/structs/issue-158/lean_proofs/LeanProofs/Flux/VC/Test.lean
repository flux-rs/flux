import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (v₀ : Int),
  (v₀ > 0) ->
   (0 ≤ v₀) ->
    ((0 < v₀)) ∧
    (∀ (v₁ : Int),
     (v₁ ≥ 0) ->
      ((k0 v₁ v₀))) ∧
    (∀ (a'₂ : Int),
     ((k0 a'₂ v₀)) ->
      (a'₂ ≥ 0)) ∧
    (((k0 0 v₀)))
    
end F
