import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#11}MAX
import LeanFixpoint
open Classical

namespace F



def TestCheckedMulUsize := ∃ k0 : (a0 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  (a'₀ = (3 * 4)) ->
   ((k0 a'₀))) ∧
 ((((3 * 4) ≤ num_{impl#11}_MAX) = True)) ∧
 (∀ (a'₁ : Int),
  ((k0 a'₁)) ->
   (a'₁ ≥ 0) ->
    (((a'₁ = 12) = True)) ∧
    (((¬((18446744073709551615 * 2) ≤ num_{impl#11}_MAX)) = True))
    )
 
end F
