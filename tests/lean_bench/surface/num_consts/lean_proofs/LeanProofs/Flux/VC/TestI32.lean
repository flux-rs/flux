import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#2}MIN
import LeanProofs.Flux.Fun.Num{impl#2}MAX
import LeanFixpoint
open Classical

namespace F



def TestI32 := 
 (((-2147483648) = num_{impl#2}_MIN)) ∧
 ((2147483647 = num_{impl#2}_MAX))
 
end F
