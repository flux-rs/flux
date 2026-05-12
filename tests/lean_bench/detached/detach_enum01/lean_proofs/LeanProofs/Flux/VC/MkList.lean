import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def MkList := 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   ((n₀ ≠ 0) ->
    (((n₀ - 1) ≥ 0)) ∧
    (((n₀ - 1) ≥ 0) ->
     (((n₀ - 1) + 1) ≥ 0) ->
      (((n₀ - 1) + 1) = n₀))
    ) ∧
   ((¬(n₀ ≠ 0)) ->
    (0 = n₀))
   
end F
