import Surface.BitvecConst00.Flux.Prelude
import Surface.BitvecConst00.Flux.Fun.START
open Classical
set_option linter.unusedVariables false


namespace F



def Test1 := 
 ((BitVec.ofInt 32 17767) = START)
end F
