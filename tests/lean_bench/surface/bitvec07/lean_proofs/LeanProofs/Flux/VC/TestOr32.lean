import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestOr32 := 
 ((BitVec.or 4#32 (BitVec.ofInt 32 1)) = 5#32)
end F
