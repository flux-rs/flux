import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl6MIN
import LeanProofs.Flux.Fun.NumImpl6MAX
import LeanFixpoint
open Classical

namespace F



def TestBothBoundedSuErrHigh := 
 ∀ (x₀ : Int),
  (x₀ > 255) ->
   ((¬((num_impl_6_MIN ≤ x₀) ∧ (x₀ ≤ num_impl_6_MAX))) = True)
end F
