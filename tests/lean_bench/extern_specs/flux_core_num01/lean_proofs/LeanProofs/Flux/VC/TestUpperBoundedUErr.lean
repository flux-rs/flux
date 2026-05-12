import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl8MAX
import LeanFixpoint
open Classical

namespace F



def TestUpperBoundedUErr := 
 ∀ (x₀ : Int),
  (x₀ ≥ 0) ->
   (x₀ > 4294967295) ->
    ((¬(x₀ ≤ num_impl_8_MAX)) = True)
end F
