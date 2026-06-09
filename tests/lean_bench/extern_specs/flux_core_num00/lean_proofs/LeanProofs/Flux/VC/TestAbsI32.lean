import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl2MIN
open Classical
set_option linter.unusedVariables false


namespace F



def TestAbsI32 := 
 (((if ((-10) > num_impl_2_MIN) then (-(-10)) else (-10)) = 10) = True)
end F
