import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl3MIN
import LeanProofs.Flux.Fun.NumImpl3MAX
import LeanFixpoint
open Classical

namespace F



def TestI64 := 
 (((-9223372036854775808) = num_impl_3_MIN)) ∧
 ((9223372036854775807 = num_impl_3_MAX))
 
end F
