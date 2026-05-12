import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl2MIN
import LeanProofs.Flux.Fun.NumImpl2MAX
import LeanFixpoint
open Classical

namespace F



def TestI32 := 
 (((-2147483648) = num_impl_2_MIN)) ∧
 ((2147483647 = num_impl_2_MAX))
 
end F
