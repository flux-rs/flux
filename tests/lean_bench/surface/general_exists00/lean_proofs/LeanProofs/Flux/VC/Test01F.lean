import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test01F := 
 ∀ (a₀ : Int),
  (a₀ > 0) ->
   (a₀ ≥ 0)
end F
