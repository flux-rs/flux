import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test00 := ¬
 ∀ (x₀ : Int),
  ((x₀ + 2) = (x₀ + 1))
end F
