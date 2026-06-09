import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestShlA := 
 ∀ (x₀ : BitVec 32),
  (x₀ = 1#32) ->
   ((BitVec_shiftLeft x₀ 3#32) = 8#32)
end F
