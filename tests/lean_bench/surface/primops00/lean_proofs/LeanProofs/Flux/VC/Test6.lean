import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test6 := 
 ∀ (c₀ : Int),
  (c₀ ≤ 1114111) ->
   (0 ≤ c₀) ->
    (((0 ≤ c₀) ∧ (c₀ ≤ 1114111)) -> ((0 ≤ (c0 c₀ 1)) ∧ ((c0 c₀ 1) ≤ 1114111))) ->
     (((c0 c₀ 1) ≤ 1114111) = True)
end F
