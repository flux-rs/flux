import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl1MIN
import LeanProofs.Flux.Fun.NumImpl1MAX
open Classical
set_option linter.unusedVariables false


namespace F



def TestI16 := 
 (((-32768) = num_impl_1_MIN)) ∧
 ((32767 = num_impl_1_MAX))
 
end F
