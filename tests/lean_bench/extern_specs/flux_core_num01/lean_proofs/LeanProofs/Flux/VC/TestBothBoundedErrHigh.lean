import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl2MIN
import LeanProofs.Flux.Fun.NumImpl2MAX
import LeanFixpoint
open Classical

namespace F



def TestBothBoundedErrHigh := 
 ∀ (x₀ : Int),
  (x₀ > 2147483647) ->
   ((¬((num_impl_2_MIN ≤ x₀) ∧ (x₀ ≤ num_impl_2_MAX))) = True)
end F
