import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#9}MIN
import LeanProofs.Flux.Fun.Num{impl#9}MAX
import LeanFixpoint
open Classical

namespace F



def TestU64 := 
 ((0 = num_{impl#9}_MIN)) ∧
 ((18446744073709551615 = num_{impl#9}_MAX))
 
end F
