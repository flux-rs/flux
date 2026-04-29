import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test := 
 ∀ (k₀ : Int),
  (k₀ < (k₀ + 1))
end F
