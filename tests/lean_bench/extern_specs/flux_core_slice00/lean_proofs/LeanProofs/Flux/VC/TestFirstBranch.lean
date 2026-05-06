import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestFirstBranch := 
 ∀ (a'₀ : Int),
  (a'₀ ≥ 0) ->
   (a'₀ > 0) ->
    ((a'₀ ≠ 0) = True)
end F
