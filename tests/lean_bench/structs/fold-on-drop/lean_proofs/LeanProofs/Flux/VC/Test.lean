import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test := 
 ∀ (s₀ : Int),
  (s₀ ≥ 0) ->
   ((s₀ + 1) ≥ 0)
end F
