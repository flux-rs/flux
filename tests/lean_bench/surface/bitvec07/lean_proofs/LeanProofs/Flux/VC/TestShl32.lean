import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestShl32 := 
 ((BitVec_shiftLeft 1#32 (BitVec.ofInt 32 3)) = 8#32)
end F
