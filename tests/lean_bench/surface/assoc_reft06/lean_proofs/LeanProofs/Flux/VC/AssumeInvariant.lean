import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def AssumeInvariant := 
 ∀ (s₀ : Int),
  (s₀ > 0) ->
   ((s₀ > 0) = True)
end F
