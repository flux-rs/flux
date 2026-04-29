import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def UintUintLossy := 
 ∀ (n₀ : Int),
  (n₀ < 100) ->
   (n₀ ≥ 0) ->
    ∀ (a'₀ : Int),
     (a'₀ ≥ 0) ->
      ((n₀ ≤ 4294967295) -> (a'₀ = n₀)) ->
       (a'₀ < 100)
end F
