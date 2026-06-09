import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.START
open Classical
set_option linter.unusedVariables false


namespace F



def Test2 := 
 ((BitVec.ofInt 32 17767) = START)
end F
