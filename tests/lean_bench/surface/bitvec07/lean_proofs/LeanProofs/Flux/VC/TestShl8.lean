import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestShl8 := 
 ((BitVec_shiftLeft 1#8 (BitVec.ofInt 8 3)) = 8#8)
end F
