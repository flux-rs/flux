import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Const.PrimOpBitAndInt
import LeanFixpoint
open Classical

namespace F



def Test4 := 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   ((PrimOpBitAndInt n₀ 7) ≤ 7) ->
    ((PrimOpBitAndInt n₀ 7) < 10)
end F
