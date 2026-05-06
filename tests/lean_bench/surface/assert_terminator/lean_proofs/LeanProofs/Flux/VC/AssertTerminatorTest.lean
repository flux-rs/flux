import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def AssertTerminatorTest := 
 ∀ (v₀ : Int),
  ∀ (a₀ : Int),
   (v₀ > 0) ->
    (a₀ ≥ 0) ->
     (v₀ ≥ 0) ->
      (v₀ ≠ 0)
end F
