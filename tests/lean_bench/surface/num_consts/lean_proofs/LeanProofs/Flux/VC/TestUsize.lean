import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#11}MIN
import LeanProofs.Flux.Fun.Num{impl#11}MAX
import LeanFixpoint
open Classical

namespace F



def TestUsize := 
 ((0 = num_{impl#11}_MIN)) ∧
 ((18446744073709551615 = num_{impl#11}_MAX))
 
end F
