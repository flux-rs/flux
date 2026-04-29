import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#3}MIN
import LeanProofs.Flux.Fun.Num{impl#3}MAX
import LeanFixpoint
open Classical

namespace F



def TestI64 := 
 (((-9223372036854775808) = num_{impl#3}_MIN)) ∧
 ((9223372036854775807 = num_{impl#3}_MAX))
 
end F
