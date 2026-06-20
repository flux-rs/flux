import Surface.Primops00.Flux.Prelude
import Surface.Primops00.Flux.Const.PrimOpBitShlInt
open Classical
set_option linter.unusedVariables false


namespace F



def Test0 := 
 ((PrimOpBitShlInt 1 2) = (4 * 1)) ->
  (((PrimOpBitShlInt 1 2) = 4) = True)
end F
