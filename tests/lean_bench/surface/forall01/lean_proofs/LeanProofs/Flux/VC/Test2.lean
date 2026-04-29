import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test2 := 
 ∀ (a'₀ : Int),
  (a'₀ ≥ 0) ->
   (a'₀ > (-1))
end F
