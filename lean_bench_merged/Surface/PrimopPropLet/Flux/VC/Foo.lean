import Surface.PrimopPropLet.Flux.Prelude
import Surface.PrimopPropLet.Flux.Const.PrimOpBitShlInt
open Classical
set_option linter.unusedVariables false


namespace F



def Foo := 
 (let a'₀ := 2; (let a'₁ := 4; ((PrimOpBitShlInt 1 a'₀) = (a'₁ * 1)))) ->
  ((PrimOpBitShlInt 1 2) = 4)
end F
