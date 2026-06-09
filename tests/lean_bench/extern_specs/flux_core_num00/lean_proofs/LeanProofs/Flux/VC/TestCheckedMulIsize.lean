import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl5MIN
import LeanProofs.Flux.Fun.NumImpl5MAX
open Classical
set_option linter.unusedVariables false


namespace F



def TestCheckedMulIsize := ∃ k0 : (a0 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  (a'₀ = (3 * 4)) ->
   ((k0 a'₀))) ∧
 (((((3 * 4) ≥ num_impl_5_MIN) ∧ ((3 * 4) ≤ num_impl_5_MAX)) = True)) ∧
 (∀ (a'₁ : Int),
  ((k0 a'₁)) ->
   (((a'₁ = 12) = True)) ∧
   (((¬(((9223372036854775807 * 2) ≥ num_impl_5_MIN) ∧ ((9223372036854775807 * 2) ≤ num_impl_5_MAX))) = True)) ∧
   (((¬((((-9223372036854775808) * 2) ≥ num_impl_5_MIN) ∧ (((-9223372036854775808) * 2) ≤ num_impl_5_MAX))) = True))
   )
 
end F
