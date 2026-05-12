import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def GeImp := 
 ∀ (x₀ : BitVec 32),
  ∀ (y₀ : BitVec 32),
   ((BitVec_uge x₀ y₀) ∧ (BitVec_uge y₀ (BitVec.ofInt 32 32)) ∧ (BitVec.ule x₀ (BitVec.ofInt 32 255))) ->
    ((BitVec_uge (BitVec.add x₀ (BitVec.ofInt 32 32)) (BitVec.sub y₀ (BitVec.ofInt 32 32))) = True)
end F
