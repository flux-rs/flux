import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestShl32 := 
 ((BitVec_shiftLeft 1#32 (BitVec.ofInt 32 3)) = 8#32)
end F
