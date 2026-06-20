import Surface.Primops00.Flux.Prelude
import Surface.Primops00.Flux.Const.PrimOpBitShlInt
open Classical
set_option linter.unusedVariables false


namespace F



def Test2 := 
 ∀ (x₀ : Int),
  (x₀ ≥ 0) ->
   ((PrimOpBitShlInt x₀ 2) = (4 * x₀)) ->
    ((PrimOpBitShlInt (PrimOpBitShlInt x₀ 2) 2) = (4 * (PrimOpBitShlInt x₀ 2))) ->
     ((PrimOpBitShlInt (PrimOpBitShlInt x₀ 2) 2) = (16 * x₀))
end F
