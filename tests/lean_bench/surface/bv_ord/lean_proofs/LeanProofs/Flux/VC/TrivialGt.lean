import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TrivialGt := 
 ∀ (x₀ : BitVec 32),
  ((BitVec.ult x₀ x₀) = (BitVec_ugt x₀ x₀))
end F
