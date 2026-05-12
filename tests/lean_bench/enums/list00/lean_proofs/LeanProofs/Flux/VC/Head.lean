import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Head := 
 ∀ (n₀ : Int),
  (0 < n₀) ->
   (n₀ ≥ 0) ->
    (n₀ = 0) ->
     False
end F
