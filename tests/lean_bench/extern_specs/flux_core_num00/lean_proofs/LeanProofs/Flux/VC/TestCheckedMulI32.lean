import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.Num{impl#2}MIN
import LeanProofs.Flux.Fun.Num{impl#2}MAX
import LeanFixpoint
open Classical

namespace F



def TestCheckedMulI32 := ∃ k0 : (a0 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  (a'₀ = (3 * 4)) ->
   ((k0 a'₀))) ∧
 (((((3 * 4) ≥ num_{impl#2}_MIN) ∧ ((3 * 4) ≤ num_{impl#2}_MAX)) = True)) ∧
 (∀ (a'₁ : Int),
  ((k0 a'₁)) ->
   (((a'₁ = 12) = True)) ∧
   (((¬(((2147483647 * 2) ≥ num_{impl#2}_MIN) ∧ ((2147483647 * 2) ≤ num_{impl#2}_MAX))) = True)) ∧
   (((¬((((-2147483648) * 2) ≥ num_{impl#2}_MIN) ∧ (((-2147483648) * 2) ≤ num_{impl#2}_MAX))) = True))
   )
 
end F
