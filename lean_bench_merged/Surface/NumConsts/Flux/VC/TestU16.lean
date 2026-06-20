import Surface.NumConsts.Flux.Prelude
import Surface.NumConsts.Flux.Fun.NumImpl7MIN
import Surface.NumConsts.Flux.Fun.NumImpl7MAX
open Classical
set_option linter.unusedVariables false


namespace F



def TestU16 := 
 ((0 = num_impl_7_MIN)) ∧
 ((65535 = num_impl_7_MAX))
 
end F
