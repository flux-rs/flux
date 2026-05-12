import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl6MIN
import LeanProofs.Flux.Fun.NumImpl6MAX
import LeanFixpoint
open Classical

namespace F



def TestU8 := 
 ((0 = num_impl_6_MIN)) ∧
 ((255 = num_impl_6_MAX))
 
end F
