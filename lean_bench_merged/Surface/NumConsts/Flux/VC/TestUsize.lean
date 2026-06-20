import Surface.NumConsts.Flux.Prelude
import Surface.NumConsts.Flux.Fun.NumImpl11MIN
import Surface.NumConsts.Flux.Fun.NumImpl11MAX
open Classical
set_option linter.unusedVariables false


namespace F



def TestUsize := 
 ((0 = num_impl_11_MIN)) ∧
 ((18446744073709551615 = num_impl_11_MAX))
 
end F
