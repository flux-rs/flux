import ExternSpecs.FluxCoreNum01.Flux.Prelude
import ExternSpecs.FluxCoreNum01.Flux.Fun.NumImpl2MIN
import ExternSpecs.FluxCoreNum01.Flux.Fun.NumImpl2MAX
open Classical
set_option linter.unusedVariables false


namespace F



def TestIntoBothBoundedErrLow := 
 ∀ (x₀ : Int),
  (x₀ < (-2147483648)) ->
   ∀ (r₀ : Prop),
    (r₀ = ((num_impl_2_MIN ≤ x₀) ∧ (x₀ ≤ num_impl_2_MAX))) ->
     ((¬r₀) = True)
end F
