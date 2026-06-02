import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Const.PrimOpBitShlInt
import LeanFixpoint
open Classical

namespace F



def Test1 := 
 ((PrimOpBitShlInt 1 2) = (4 * 1)) ->
  ((PrimOpBitShlInt (PrimOpBitShlInt 1 2) 2) = (4 * (PrimOpBitShlInt 1 2))) ->
   (((PrimOpBitShlInt (PrimOpBitShlInt 1 2) 2) = 16) = True)
end F
