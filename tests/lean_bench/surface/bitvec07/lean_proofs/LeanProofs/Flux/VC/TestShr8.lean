import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestShr8 := 
 ((BitVec_ushiftRight 8#8 (BitVec.ofInt 8 3)) = 1#8)
end F
