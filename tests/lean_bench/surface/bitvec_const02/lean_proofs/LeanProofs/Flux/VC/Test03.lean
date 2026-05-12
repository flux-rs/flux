import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test03 := 
 ∀ (x₀ : Int),
  ((x₀ + 3) = (x₀ + (1 + 2)))
end F
