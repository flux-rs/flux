import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl5MIN
import LeanProofs.Flux.Fun.NumImpl5MAX
import LeanFixpoint
open Classical

namespace F



def TestCheckedIsize := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  (a'₀ = ((9223372036854775807 - 1) + 1)) ->
   ((k0 a'₀))) ∧
 ((((((9223372036854775807 - 1) + 1) ≥ num_impl_5_MIN) ∧ (((9223372036854775807 - 1) + 1) ≤ num_impl_5_MAX)) = True)) ∧
 (∀ (a'₁ : Int),
  ((k0 a'₁)) ->
   (((a'₁ = 9223372036854775807) = True)) ∧
   (((¬(((9223372036854775807 + 1) ≥ num_impl_5_MIN) ∧ ((9223372036854775807 + 1) ≤ num_impl_5_MAX))) = True)) ∧
   (((¬((((-9223372036854775808) + (-1)) ≥ num_impl_5_MIN) ∧ (((-9223372036854775808) + (-1)) ≤ num_impl_5_MAX))) = True)) ∧
   (∀ (a'₂ : Int),
    (a'₂ = (5 - 3)) ->
     ((k1 a'₂ a'₁))) ∧
   (((((5 - 3) ≥ num_impl_5_MIN) ∧ ((5 - 3) ≤ num_impl_5_MAX)) = True)) ∧
   (∀ (a'₃ : Int),
    ((k1 a'₃ a'₁)) ->
     (((a'₃ = 2) = True)) ∧
     (((¬((((-9223372036854775808) - 1) ≥ num_impl_5_MIN) ∧ (((-9223372036854775808) - 1) ≤ num_impl_5_MAX))) = True)) ∧
     (((¬(((9223372036854775807 - (-1)) ≥ num_impl_5_MIN) ∧ ((9223372036854775807 - (-1)) ≤ num_impl_5_MAX))) = True))
     )
   )
 
end F
