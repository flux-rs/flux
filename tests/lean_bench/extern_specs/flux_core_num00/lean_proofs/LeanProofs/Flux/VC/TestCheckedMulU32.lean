import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl8MAX
import LeanFixpoint
open Classical

namespace F



def TestCheckedMulU32 := ∃ k0 : (a0 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  (a'₀ = (3 * 4)) ->
   ((k0 a'₀))) ∧
 ((((3 * 4) ≤ num_impl_8_MAX) = True)) ∧
 (∀ (a'₁ : Int),
  ((k0 a'₁)) ->
   (a'₁ ≥ 0) ->
    (((a'₁ = 12) = True)) ∧
    (((¬((4294967295 * 2) ≤ num_impl_8_MAX)) = True))
    )
 
end F
