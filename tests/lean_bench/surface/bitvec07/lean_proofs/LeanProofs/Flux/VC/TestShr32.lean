import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestShr32 := 
 ((BitVec_ushiftRight 8#32 (BitVec.ofInt 32 3)) = 1#32)
end F
