import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#6}MIN
import LeanProofs.Flux.Fun.Num{impl#6}MAX
import LeanFixpoint
open Classical

namespace F



def TestBothBoundedSuErrHigh := 
 ∀ (x₀ : Int),
  (x₀ > 255) ->
   ((¬((num_{impl#6}_MIN ≤ x₀) ∧ (x₀ ≤ num_{impl#6}_MAX))) = True)
end F
