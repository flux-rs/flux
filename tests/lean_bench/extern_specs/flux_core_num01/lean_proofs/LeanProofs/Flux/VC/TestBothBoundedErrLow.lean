import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#2}MIN
import LeanProofs.Flux.Fun.Num{impl#2}MAX
import LeanFixpoint
open Classical

namespace F



def TestBothBoundedErrLow := 
 ∀ (x₀ : Int),
  (x₀ < (-2147483648)) ->
   ((¬((num_{impl#2}_MIN ≤ x₀) ∧ (x₀ ≤ num_{impl#2}_MAX))) = True)
end F
