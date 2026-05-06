import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestMapBranch := 
 ∀ (x₀ : Prop),
  ((x₀ = x₀) = True)
end F
