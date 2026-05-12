import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestString := 
 (((0 + 1) + 1) ≥ 0) ->
  ((((0 + 1) + 1) = 2)) ∧
  ((((0 + 1) + 1) > 0)) ∧
  (((((0 + 1) + 1) - 1) ≥ 0) ->
   (((((0 + 1) + 1) - 1) = 1)) ∧
   (((((0 + 1) + 1) - 1) > 0)) ∧
   ((((((0 + 1) + 1) - 1) - 1) = 0)) ∧
   ((((((0 + 1) + 1) - 1) - 1) ≥ 0) ->
    (((((0 + 1) + 1) - 1) - 1) = 0))
   )
  
end F
