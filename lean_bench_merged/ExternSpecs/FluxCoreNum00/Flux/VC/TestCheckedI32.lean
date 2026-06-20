import ExternSpecs.FluxCoreNum00.Flux.Prelude
import ExternSpecs.FluxCoreNum00.Flux.Fun.NumImpl2MIN
import ExternSpecs.FluxCoreNum00.Flux.Fun.NumImpl2MAX
open Classical
set_option linter.unusedVariables false


namespace F



def TestCheckedI32 := ∃ k0 : (a0 : Int) -> Prop, ∃ k1 : (a0 : Int) -> (a1 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  (a'₀ = ((2147483647 - 1) + 1)) ->
   ((k0 a'₀))) ∧
 ((((((2147483647 - 1) + 1) ≥ num_impl_2_MIN) ∧ (((2147483647 - 1) + 1) ≤ num_impl_2_MAX)) = True)) ∧
 (∀ (a'₁ : Int),
  ((k0 a'₁)) ->
   (((a'₁ = 2147483647) = True)) ∧
   (((¬(((2147483647 + 1) ≥ num_impl_2_MIN) ∧ ((2147483647 + 1) ≤ num_impl_2_MAX))) = True)) ∧
   (((¬((((-2147483648) + (-1)) ≥ num_impl_2_MIN) ∧ (((-2147483648) + (-1)) ≤ num_impl_2_MAX))) = True)) ∧
   (∀ (a'₂ : Int),
    (a'₂ = (5 - 3)) ->
     ((k1 a'₂ a'₁))) ∧
   (((((5 - 3) ≥ num_impl_2_MIN) ∧ ((5 - 3) ≤ num_impl_2_MAX)) = True)) ∧
   (∀ (a'₃ : Int),
    ((k1 a'₃ a'₁)) ->
     (((a'₃ = 2) = True)) ∧
     (((¬((((-2147483648) - 1) ≥ num_impl_2_MIN) ∧ (((-2147483648) - 1) ≤ num_impl_2_MAX))) = True)) ∧
     (((¬(((2147483647 - (-1)) ≥ num_impl_2_MIN) ∧ ((2147483647 - (-1)) ≤ num_impl_2_MAX))) = True))
     )
   )
 
end F
