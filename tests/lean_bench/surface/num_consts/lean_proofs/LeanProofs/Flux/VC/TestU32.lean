import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#8}MIN
import LeanProofs.Flux.Fun.Num{impl#8}MAX
import LeanFixpoint
open Classical

namespace F



def TestU32 := 
 ((0 = num_{impl#8}_MIN)) ∧
 ((4294967295 = num_{impl#8}_MAX))
 
end F
