import Surface.NumConsts.Flux.Prelude
import Surface.NumConsts.Flux.Fun.NumImpl5MIN
import Surface.NumConsts.Flux.Fun.NumImpl5MAX
open Classical
set_option linter.unusedVariables false


namespace F



def TestIsize := 
 (((-9223372036854775808) = num_impl_5_MIN)) ∧
 ((9223372036854775807 = num_impl_5_MAX))
 
end F
