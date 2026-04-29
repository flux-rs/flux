import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test2 := 
 ∀ (x₀ : Int),
  (x₀ ≥ 0) ->
   ((c0 x₀ 2) = (4 * x₀)) ->
    ((c0 (c0 x₀ 2) 2) = (4 * (c0 x₀ 2))) ->
     ((c0 (c0 x₀ 2) 2) = (16 * x₀))
end F
