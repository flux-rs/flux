import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def IsZero := 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   ((n₀ + 1) > 0)
end F
