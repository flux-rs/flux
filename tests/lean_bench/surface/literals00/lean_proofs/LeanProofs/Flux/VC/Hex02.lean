import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Hex02 := 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   (((n₀ + 1000) + 24) = (n₀ + 1024))
end F
