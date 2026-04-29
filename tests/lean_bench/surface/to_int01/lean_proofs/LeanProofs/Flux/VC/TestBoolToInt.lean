import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestBoolToInt := 
 ∀ (x₀ : Prop),
  ((if x₀ then 1 else 0) = (if x₀ then 1 else 0))
end F
