import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#0}MIN
import LeanProofs.Flux.Fun.Num{impl#0}MAX
import LeanFixpoint
open Classical

namespace F



def TestI8 := 
 (((-128) = num_{impl#0}_MIN)) ∧
 ((127 = num_{impl#0}_MAX))
 
end F
