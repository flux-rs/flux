import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#7}MIN
import LeanProofs.Flux.Fun.Num{impl#7}MAX
import LeanFixpoint
open Classical

namespace F



def TestU16 := 
 ((0 = num_{impl#7}_MIN)) ∧
 ((65535 = num_{impl#7}_MAX))
 
end F
