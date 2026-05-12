import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TrivialGe := 
 ∀ (x₀ : BitVec 32),
  ((BitVec.ule x₀ x₀) = (BitVec_uge x₀ x₀))
end F
