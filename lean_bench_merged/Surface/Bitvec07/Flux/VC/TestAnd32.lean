import Surface.Bitvec07.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestAnd32 := 
 ((BitVec.and 6#32 (BitVec.ofInt 32 3)) = 2#32)
end F
