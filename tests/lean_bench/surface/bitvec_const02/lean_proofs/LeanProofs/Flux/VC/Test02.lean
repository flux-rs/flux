import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test02 := 
 ∀ (x₀ : BitVec 32),
  ((BitVec.add x₀ (BitVec.ofInt 32 1)) = (BitVec.add x₀ 1#32))
end F
