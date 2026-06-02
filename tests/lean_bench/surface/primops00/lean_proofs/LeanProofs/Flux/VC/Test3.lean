import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Const.PrimOpBitShrInt
import LeanProofs.Flux.Const.PrimOpBitAndInt
import LeanFixpoint
open Classical

namespace F



def Test3 := 
 ∀ (byte₀ : Int),
  (byte₀ ≤ 127) ->
   (byte₀ ≥ 0) ->
    ((16 * (PrimOpBitShrInt byte₀ 4)) = byte₀) ->
     ((PrimOpBitAndInt byte₀ 15) ≤ 15) ->
      ((((PrimOpBitShrInt byte₀ 4) ≤ 15) = True)) ∧
      ((((PrimOpBitAndInt byte₀ 15) ≤ 15) = True))
      
end F
