import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def BobInc := 
 ∀ (n₀ : Int),
  (n₀ < (n₀ + 1))
end F
