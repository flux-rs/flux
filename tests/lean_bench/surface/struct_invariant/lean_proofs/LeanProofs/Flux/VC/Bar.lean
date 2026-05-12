import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Bar := 
 ∀ (z₀ : Int),
  (99 < z₀) ->
   (z₀ > 10)
end F
