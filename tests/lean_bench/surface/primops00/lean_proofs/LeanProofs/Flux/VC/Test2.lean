import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Const.PrimOpBitShlInt
import LeanFixpoint
open Classical

namespace F



def Test2 := 
 ∀ (x₀ : Int),
  (x₀ ≥ 0) ->
   ((PrimOpBitShlInt x₀ 2) = (4 * x₀)) ->
    ((PrimOpBitShlInt (PrimOpBitShlInt x₀ 2) 2) = (4 * (PrimOpBitShlInt x₀ 2))) ->
     ((PrimOpBitShlInt (PrimOpBitShlInt x₀ 2) 2) = (16 * x₀))
end F
