import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def ReadIx := 
 ∀ (v₀ : Int),
  ((c0 v₀) = 10) ->
   ((c0 v₀) > 0)
end F
