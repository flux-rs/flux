import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#1}MIN
import LeanProofs.Flux.Fun.Num{impl#1}MAX
import LeanFixpoint
open Classical

namespace F



def TestI16 := 
 (((-32768) = num_{impl#1}_MIN)) ∧
 ((32767 = num_{impl#1}_MAX))
 
end F
