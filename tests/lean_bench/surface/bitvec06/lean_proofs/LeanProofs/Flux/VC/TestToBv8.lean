import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestToBv8 := 
 ((BitVec.toNat (BitVec.add (BitVec.ofInt 8 1) (BitVec.ofInt 8 2))) ≥ 0) ->
  ((BitVec.toNat (BitVec.add (BitVec.ofInt 8 1) (BitVec.ofInt 8 2))) = 3)
end F
