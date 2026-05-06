import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Watermelon := 
 ∀ (n₀ : Int),
  (n₀ ≥ 0) ->
   (((n₀ + 1) + 1) = (n₀ + 2))
end F
