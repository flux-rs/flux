import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#5}MIN
import LeanFixpoint
open Classical

namespace F



def TestAbsIsize := 
 (((if ((-10) > num_{impl#5}_MIN) then (-(-10)) else (-10)) = 10) = True)
end F
