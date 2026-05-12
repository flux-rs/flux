import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test4 := 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   ((c0 n₀ 7) ≤ 7) ->
    ((c0 n₀ 7) < 10)
end F
