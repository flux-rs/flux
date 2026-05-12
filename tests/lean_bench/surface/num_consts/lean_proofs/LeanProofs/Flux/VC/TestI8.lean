import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl0MIN
import LeanProofs.Flux.Fun.NumImpl0MAX
import LeanFixpoint
open Classical

namespace F



def TestI8 := 
 (((-128) = num_impl_0_MIN)) ∧
 ((127 = num_impl_0_MAX))
 
end F
