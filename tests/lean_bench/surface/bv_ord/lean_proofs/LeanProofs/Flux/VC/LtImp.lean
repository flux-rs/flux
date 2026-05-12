import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def LtImp := 
 ∀ (x₀ : BitVec 32),
  ∀ (y₀ : BitVec 32),
   ((BitVec.ult x₀ y₀) ∧ (BitVec_ugt x₀ (BitVec.ofInt 32 32)) ∧ (BitVec.ult y₀ (BitVec.ofInt 32 255))) ->
    ((BitVec.ult (BitVec.sub x₀ (BitVec.ofInt 32 32)) (BitVec.add y₀ (BitVec.ofInt 32 32))) = True)
end F
