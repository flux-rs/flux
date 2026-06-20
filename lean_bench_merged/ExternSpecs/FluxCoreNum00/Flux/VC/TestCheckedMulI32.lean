import ExternSpecs.FluxCoreNum00.Flux.Prelude
import ExternSpecs.FluxCoreNum00.Flux.Fun.NumImpl2MIN
import ExternSpecs.FluxCoreNum00.Flux.Fun.NumImpl2MAX
open Classical
set_option linter.unusedVariables false


namespace F



def TestCheckedMulI32 := ∃ k0 : (a0 : Int) -> Prop, 
 (∀ (a'₀ : Int),
  (a'₀ = (3 * 4)) ->
   ((k0 a'₀))) ∧
 (((((3 * 4) ≥ num_impl_2_MIN) ∧ ((3 * 4) ≤ num_impl_2_MAX)) = True)) ∧
 (∀ (a'₁ : Int),
  ((k0 a'₁)) ->
   (((a'₁ = 12) = True)) ∧
   (((¬(((2147483647 * 2) ≥ num_impl_2_MIN) ∧ ((2147483647 * 2) ≤ num_impl_2_MAX))) = True)) ∧
   (((¬((((-2147483648) * 2) ≥ num_impl_2_MIN) ∧ (((-2147483648) * 2) ≤ num_impl_2_MAX))) = True))
   )
 
end F
