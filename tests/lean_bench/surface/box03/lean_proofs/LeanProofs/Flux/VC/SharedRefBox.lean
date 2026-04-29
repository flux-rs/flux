import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def SharedRefBox := 
 ∀ (v₀ : Int),
  (v₀ ≥ 0) ->
   ((v₀ + 1) > 0)
end F
