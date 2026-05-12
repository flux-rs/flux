import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl5MIN
import LeanProofs.Flux.Fun.NumImpl5MAX
import LeanFixpoint
open Classical

namespace F



def TestIsize := 
 (((-9223372036854775808) = num_impl_5_MIN)) ∧
 ((9223372036854775807 = num_impl_5_MAX))
 
end F
