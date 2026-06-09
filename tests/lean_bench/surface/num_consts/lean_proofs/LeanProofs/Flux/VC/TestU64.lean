import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl9MIN
import LeanProofs.Flux.Fun.NumImpl9MAX
open Classical
set_option linter.unusedVariables false


namespace F



def TestU64 := 
 ((0 = num_impl_9_MIN)) ∧
 ((18446744073709551615 = num_impl_9_MAX))
 
end F
