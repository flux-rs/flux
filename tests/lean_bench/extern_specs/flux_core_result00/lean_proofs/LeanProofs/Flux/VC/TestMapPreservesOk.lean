import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestMapPreservesOk := 
 ∀ (r₀ : Prop),
  ((r₀ = r₀) = True)
end F
