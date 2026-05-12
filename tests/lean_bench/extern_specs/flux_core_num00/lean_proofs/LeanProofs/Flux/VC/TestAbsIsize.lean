import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl5MIN
import LeanFixpoint
open Classical

namespace F



def TestAbsIsize := 
 (((if ((-10) > num_impl_5_MIN) then (-(-10)) else (-10)) = 10) = True)
end F
