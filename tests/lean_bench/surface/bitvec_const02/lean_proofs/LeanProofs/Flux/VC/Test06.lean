import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def Test06 := 
 ∀ (x₀ : BitVec 32),
  ∀ (y₀ : BitVec 32),
   ((BitVec_ugt (BitVec.add x₀ y₀) (BitVec.ofInt 32 5)) = (BitVec_ugt (BitVec.add x₀ y₀) 5#32))
end F
