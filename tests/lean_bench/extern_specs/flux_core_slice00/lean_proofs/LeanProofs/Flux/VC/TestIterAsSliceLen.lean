import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestIterAsSliceLen := 
 ∀ (a'₀ : Int),
  (a'₀ ≥ 0) ->
   ((a'₀ = a'₀) = True)
end F
