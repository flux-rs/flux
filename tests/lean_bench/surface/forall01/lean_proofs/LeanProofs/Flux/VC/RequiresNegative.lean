import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def RequiresNegative := 
 ∀ (x₀ : Int),
  (((x₀ + 1) = (1 + x₀)) = True)
end F
