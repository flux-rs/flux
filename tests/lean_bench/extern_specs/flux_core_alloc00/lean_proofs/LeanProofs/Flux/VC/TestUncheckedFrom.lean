import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl5MAX
import LeanFixpoint
open Classical

namespace F



def TestUncheckedFrom := 
 ((((4 + 4) - 1) ≤ num_impl_5_MAX)) ∧
 (((BitVec.and (BitVec.ofInt 64 4) (BitVec.sub (BitVec.ofInt 64 4) (BitVec.ofInt 64 1))) = (BitVec.ofInt 64 0)))
 
end F
