import Surface.NumConsts.Flux.Prelude
import Surface.NumConsts.Flux.Fun.NumImpl2MIN
import Surface.NumConsts.Flux.Fun.NumImpl2MAX
open Classical
set_option linter.unusedVariables false


namespace F



def TestI32 := 
 (((-2147483648) = num_impl_2_MIN)) ∧
 ((2147483647 = num_impl_2_MAX))
 
end F
