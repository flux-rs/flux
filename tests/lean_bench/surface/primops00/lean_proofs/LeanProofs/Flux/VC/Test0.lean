import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Const.PrimOpBitShlInt
import LeanFixpoint
open Classical

namespace F



def Test0 := 
 ((PrimOpBitShlInt 1 2) = (4 * 1)) ->
  (((PrimOpBitShlInt 1 2) = 4) = True)
end F
