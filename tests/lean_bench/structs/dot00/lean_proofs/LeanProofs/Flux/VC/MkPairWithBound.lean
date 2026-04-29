import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def MkPairWithBound := 
 ∀ (a₀ : Int),
  ((a₀ + 0) ≤ a₀)
end F
