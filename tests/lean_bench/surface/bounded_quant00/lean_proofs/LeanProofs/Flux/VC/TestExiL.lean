import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestExiL := 
 ∀ (n₀ : Int),
  ((((0 = n₀) ∨ (1 = n₀)) ∨ (2 = n₀)) ∨ (3 = n₀)) ->
   (n₀ ≠ 0) ->
    (n₀ ≠ 1) ->
     (n₀ ≠ 2) ->
      ((n₀ = 3) = True)
end F
