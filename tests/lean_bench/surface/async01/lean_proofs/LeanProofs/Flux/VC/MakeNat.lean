import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def MakeNat := 
 ∀ (n₀ : Int),
  (n₀ ≤ (n₀ + 1))
end F
