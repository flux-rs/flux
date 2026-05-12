import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl2MIN
import LeanFixpoint
open Classical

namespace F



def NegOverflowI32 := 
 ∀ (a₀ : Int),
  (a₀ ≠ num_impl_2_MIN) ->
   (a₀ ≥ (-2147483648)) ->
    (a₀ ≤ 2147483647) ->
     (a₀ ≠ (-2147483648))
end F
