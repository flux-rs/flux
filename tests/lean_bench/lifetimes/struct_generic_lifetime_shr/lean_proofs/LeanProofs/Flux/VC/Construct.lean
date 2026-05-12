import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Construct := 
 ∀ (x₀ : Int),
  (x₀ ≥ 0) ->
   ((x₀ + 1) > 0)
end F
