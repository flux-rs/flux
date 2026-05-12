import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Add := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (0 ≤ n₀) ->
   (n₀ ≥ 0) ->
    (((n₀ = n₀) = True)) ∧
    ((∀ (a'₀ : Int),
     ((k0 a'₀ n₀)) ->
      (a'₀ ≥ 0) ->
       ((a'₀ < n₀)) ∧
       (∀ (a'₁ : Int),
        (a'₀ < n₀))
       ) ∧
    (∀ (v₀ : Int),
     ((0 ≤ v₀) ∧ (v₀ < n₀)) ->
      ((k0 v₀ n₀)))
    )
    
end F
