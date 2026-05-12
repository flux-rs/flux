import LeanProofs.Flux.Prelude
import LeanFixpoint
open Classical

namespace F



def TestOr8 := 
 ((BitVec.or 4#8 (BitVec.ofInt 8 1)) = 5#8)
end F
