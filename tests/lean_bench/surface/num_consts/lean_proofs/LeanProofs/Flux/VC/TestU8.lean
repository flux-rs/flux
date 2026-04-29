import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#6}MIN
import LeanProofs.Flux.Fun.Num{impl#6}MAX
import LeanFixpoint
open Classical

namespace F



def TestU8 := 
 ((0 = num_{impl#6}_MIN)) ∧
 ((255 = num_{impl#6}_MAX))
 
end F
