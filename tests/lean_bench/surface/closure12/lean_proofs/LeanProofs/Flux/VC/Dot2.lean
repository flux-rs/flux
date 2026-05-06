import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Dot2 := ∃ k0 : (a0 : Int) -> (a1 : Int) -> Prop, 
 ∀ (n₀ : Int),
  (0 ≤ n₀) ->
   (n₀ ≥ 0) ->
    (∀ (a'₀ : Int),
     ((k0 a'₀ n₀)) ->
      (a'₀ ≥ 0) ->
       ((a'₀ < n₀)) ∧
       (∀ (a'₁ : Int),
        (a'₀ < n₀))
       ) ∧
    (∀ (item₀ : Int),
     ((0 ≤ item₀) ∧ (item₀ < n₀)) ->
      ((k0 item₀ n₀)))
    
end F
