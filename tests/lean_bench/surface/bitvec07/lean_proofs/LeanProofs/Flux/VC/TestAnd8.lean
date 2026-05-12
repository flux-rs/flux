import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestAnd8 := 
 ((BitVec.and 6#8 (BitVec.ofInt 8 3)) = 2#8)
end F
