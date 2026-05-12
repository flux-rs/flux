import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestIntoLowerBoundedErr := 
 ∀ (x₀ : Int),
  (x₀ < 0) ->
   ∀ (r₀ : Prop),
    (r₀ = (x₀ ≥ 0)) ->
     ((¬r₀) = True)
end F
