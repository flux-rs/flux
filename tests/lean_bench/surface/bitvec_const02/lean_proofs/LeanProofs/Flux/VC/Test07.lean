import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test07 := 
 ∀ (x₀ : BitVec 32),
  ∀ (y₀ : BitVec 32),
   ((BitVec_ugt (BitVec.add x₀ y₀) (BitVec.sub x₀ y₀)) = (BitVec_ugt (BitVec.add x₀ y₀) (BitVec.sub x₀ y₀)))
end F
