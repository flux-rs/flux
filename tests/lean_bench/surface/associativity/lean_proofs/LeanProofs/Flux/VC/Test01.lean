import LeanProofs.Flux.Prelude
open Classical
set_option linter.unusedVariables false


namespace F



def Test01 := 
 ((BitVec.ofInt 32 3794967296) = (BitVec.add (BitVec.sub 1000000000#32 3500000000#32) 2000000000#32))
end F
