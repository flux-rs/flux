import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.ROOTNANOSPERSEC
import LeanFixpoint
open Classical

namespace F



def Test64 := 
 ∀ (nanos₀ : Int),
  (nanos₀ ≥ 0) ->
   ((0 ≤ (nanos₀ % 1000000000))) ∧
   (((nanos₀ % 1000000000) < ROOT_NANOS_PER_SEC))
   
end F
