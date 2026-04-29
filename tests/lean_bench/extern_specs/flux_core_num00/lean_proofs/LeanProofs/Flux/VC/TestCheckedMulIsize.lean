import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#5}MIN
import LeanProofs.Flux.Fun.Num{impl#5}MAX
import LeanFixpoint
open Classical

namespace F



def TestCheckedMulIsize := ∃ k0 : (a0 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  (a'₀ = (3 * 4)) ->
   ((k0 a'₀))) ∧
 (((((3 * 4) ≥ num_{impl#5}_MIN) ∧ ((3 * 4) ≤ num_{impl#5}_MAX)) = True)) ∧
 (∀ (a'₁ : Int),
  ((k0 a'₁)) ->
   (((a'₁ = 12) = True)) ∧
   (((¬(((9223372036854775807 * 2) ≥ num_{impl#5}_MIN) ∧ ((9223372036854775807 * 2) ≤ num_{impl#5}_MAX))) = True)) ∧
   (((¬((((-9223372036854775808) * 2) ≥ num_{impl#5}_MIN) ∧ (((-9223372036854775808) * 2) ≤ num_{impl#5}_MAX))) = True))
   )
 
end F
