import Surface.Bitvec07.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestShl8 := 
 ((BitVec_shiftLeft 1#8 (BitVec.ofInt 8 3)) = 8#8)
end F
