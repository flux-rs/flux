import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestLowerBoundedErr := 
 ∀ (x₀ : Int),
  (x₀ < 0) ->
   ((¬(x₀ ≥ 0)) = True)
end F
