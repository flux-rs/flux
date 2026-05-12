import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl7MIN
import LeanProofs.Flux.Fun.NumImpl7MAX
import LeanFixpoint
open Classical

namespace F



def TestU16 := 
 ((0 = num_impl_7_MIN)) ∧
 ((65535 = num_impl_7_MAX))
 
end F
