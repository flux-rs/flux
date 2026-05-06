import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test01 := 
 ∀ (x₀ : Real),
  ((x₀ + 1.0) > x₀)
end F
