import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl5MAX
import LeanFixpoint
open Classical

namespace F



def TestFromValid := 
 ((((((4 + 4) - 1) ≤ num_impl_5_MAX) ∧ ((BitVec.and (BitVec.ofInt 64 4) (BitVec.sub (BitVec.ofInt 64 4) (BitVec.ofInt 64 1))) = (BitVec.ofInt 64 0))) = True)) ∧
 ((((((0 + 8) - 1) ≤ num_impl_5_MAX) ∧ ((BitVec.and (BitVec.ofInt 64 8) (BitVec.sub (BitVec.ofInt 64 8) (BitVec.ofInt 64 1))) = (BitVec.ofInt 64 0))) = True)) ∧
 (∀ (a'₀ : Int),
  (a'₀ ≥ 0) ->
   (True -> (a'₀ = 9223372036854775807)) ->
    (((a'₀ - 7) ≥ 0)) ∧
    (((((((a'₀ - 7) + 8) - 1) ≤ num_impl_5_MAX) ∧ ((BitVec.and (BitVec.ofInt 64 8) (BitVec.sub (BitVec.ofInt 64 8) (BitVec.ofInt 64 1))) = (BitVec.ofInt 64 0))) = True))
    )
 
end F
