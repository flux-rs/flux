import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#2}MIN
import LeanFixpoint
open Classical

namespace F



def TestAbsI32 := 
 (((if ((-10) > num_{impl#2}_MIN) then (-(-10)) else (-10)) = 10) = True)
end F
