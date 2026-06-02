import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Const.PrimOpBitXorInt
import LeanFixpoint
open Classical

namespace F



def Test5 := 
 ∀ (x₀ : Int),
  (x₀ ≥ 0) ->
   ((x₀ = x₀) -> ((PrimOpBitXorInt x₀ x₀) = 0)) ->
    ((PrimOpBitXorInt x₀ x₀) = 0)
end F
