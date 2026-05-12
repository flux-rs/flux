import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestAnd32 := 
 ((BitVec.and 6#32 (BitVec.ofInt 32 3)) = 2#32)
end F
