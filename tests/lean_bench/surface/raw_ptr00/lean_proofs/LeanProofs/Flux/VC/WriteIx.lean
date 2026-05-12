import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def WriteIx := 
 ∀ (v₀ : Int),
  ∀ (value₀ : Int),
   ((c0 v₀) = 99) ->
    ((c0 v₀) > 0)
end F
