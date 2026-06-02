import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Const.PrimOpBitShlInt
import LeanFixpoint
open Classical

namespace F



def Foo := 
 (let a'₀ := 2; (let a'₁ := 4; ((PrimOpBitShlInt 1 a'₀) = (a'₁ * 1)))) ->
  ((PrimOpBitShlInt 1 2) = 4)
end F
