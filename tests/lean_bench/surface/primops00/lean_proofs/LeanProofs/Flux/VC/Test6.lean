import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Const.PrimOpBitOrInt
import LeanFixpoint
open Classical

namespace F



def Test6 := 
 ∀ (c₀ : Int),
  (c₀ ≤ 1114111) ->
   (0 ≤ c₀) ->
    (((0 ≤ c₀) ∧ (c₀ ≤ 1114111)) -> ((0 ≤ (PrimOpBitOrInt c₀ 1)) ∧ ((PrimOpBitOrInt c₀ 1) ≤ 1114111))) ->
     (((PrimOpBitOrInt c₀ 1) ≤ 1114111) = True)
end F
