import Surface.Bitvec07.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def TestOr8 := 
 ((BitVec.or 4#8 (BitVec.ofInt 8 1)) = 5#8)
end F
