import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test2 := 
 ∀ (v₀ : Int),
  (10 ≤ v₀) ->
   ((v₀ + 1) ≥ 10)
end F
