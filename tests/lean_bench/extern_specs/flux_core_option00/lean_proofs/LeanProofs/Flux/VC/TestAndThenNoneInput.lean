import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestAndThenNoneInput := 
 ∀ (s₀ : Prop),
  (s₀ -> False) ->
   ((¬s₀) = True)
end F
