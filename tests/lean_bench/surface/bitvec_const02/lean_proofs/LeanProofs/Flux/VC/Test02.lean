import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test02 := 
 ∀ (x₀ : BitVec 32),
  ((BitVec.add x₀ (BitVec.ofInt 32 1)) = (BitVec.add x₀ 1#32))
end F
