import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#2}MIN
import LeanFixpoint
open Classical

namespace F



def NegOverflowI32 := 
 ∀ (a₀ : Int),
  (a₀ ≠ num_{impl#2}_MIN) ->
   (a₀ ≥ (-2147483648)) ->
    (a₀ ≤ 2147483647) ->
     (a₀ ≠ (-2147483648))
end F
