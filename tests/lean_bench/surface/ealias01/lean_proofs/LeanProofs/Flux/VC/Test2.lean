import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test2 := 
 ∀ (v₀ : Int),
  (0 ≤ v₀) ->
   ((v₀ + 1) ≥ 0)
end F
