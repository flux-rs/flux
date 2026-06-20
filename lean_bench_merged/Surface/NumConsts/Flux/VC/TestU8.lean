import Surface.NumConsts.Flux.Prelude
import Surface.NumConsts.Flux.Fun.NumImpl6MIN
import Surface.NumConsts.Flux.Fun.NumImpl6MAX
open Classical
set_option linter.unusedVariables false


namespace F



def TestU8 := 
 ((0 = num_impl_6_MIN)) ∧
 ((255 = num_impl_6_MAX))
 
end F
