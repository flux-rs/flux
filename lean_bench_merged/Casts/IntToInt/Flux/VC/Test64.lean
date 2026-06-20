import Casts.IntToInt.Flux.Prelude
import Casts.IntToInt.Flux.Fun.ROOTNANOSPERSEC
open Classical
set_option linter.unusedVariables false


namespace F



def Test64 := 
 ∀ (nanos₀ : Int),
  (nanos₀ ≥ 0) ->
   ((0 ≤ (nanos₀ % 1000000000))) ∧
   (((nanos₀ % 1000000000) < ROOT_NANOS_PER_SEC))
   
end F
