import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestShr8 := 
 ((BitVec_ushiftRight 8#8 (BitVec.ofInt 8 3)) = 1#8)
end F
