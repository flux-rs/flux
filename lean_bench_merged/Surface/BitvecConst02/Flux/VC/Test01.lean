import Surface.BitvecConst02.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test01 := 
 ∀ (x₀ : BitVec 32),
  ((BitVec.add x₀ (BitVec.ofInt 32 1)) = (BitVec.add x₀ (BitVec.ofInt 32 1)))
end F
