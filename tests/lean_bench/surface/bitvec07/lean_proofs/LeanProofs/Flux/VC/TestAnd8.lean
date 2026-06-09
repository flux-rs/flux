import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestAnd8 := 
 ((BitVec.and 6#8 (BitVec.ofInt 8 3)) = 2#8)
end F
