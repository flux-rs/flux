import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestShr32 := 
 ((BitVec_ushiftRight 8#32 (BitVec.ofInt 32 3)) = 1#32)
end F
