import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Tail := 
 ∀ (n₀ : Int),
  (0 < n₀) ->
   (n₀ ≥ 0) ->
    (n₀ = 0) ->
     False
end F
