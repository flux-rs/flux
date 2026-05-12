import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl8MIN
import LeanProofs.Flux.Fun.NumImpl8MAX
import LeanFixpoint
open Classical

namespace F



def TestU32 := 
 ((0 = num_impl_8_MIN)) ∧
 ((4294967295 = num_impl_8_MAX))
 
end F
