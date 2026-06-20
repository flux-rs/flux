import Surface.Bitvec05.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TheoremPow2Octet := 
 ∀ (x₀ : BitVec 32),
  ((BitVec_ugt x₀ 0#32) ∧ ((BitVec.and x₀ (BitVec.sub x₀ 1#32)) = 0#32) ∧ (BitVec.ule 8#32 x₀)) ->
   ((BitVec.umod x₀ 8#32) = 0#32)
end F
