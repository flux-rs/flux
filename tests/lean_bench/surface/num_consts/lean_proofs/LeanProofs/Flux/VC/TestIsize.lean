import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#5}MIN
import LeanProofs.Flux.Fun.Num{impl#5}MAX
import LeanFixpoint
open Classical

namespace F



def TestIsize := 
 (((-9223372036854775808) = num_{impl#5}_MIN)) ∧
 ((9223372036854775807 = num_{impl#5}_MAX))
 
end F
