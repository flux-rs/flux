import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#8}MAX
import LeanFixpoint
open Classical

namespace F



def TestUpperBoundedUErr := 
 ∀ (x₀ : Int),
  (x₀ ≥ 0) ->
   (x₀ > 4294967295) ->
    ((¬(x₀ ≤ num_{impl#8}_MAX)) = True)
end F
