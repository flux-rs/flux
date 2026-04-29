import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Dec := 
 ∀ (x₀ : Int),
  ((x₀ - 1) < x₀)
end F
