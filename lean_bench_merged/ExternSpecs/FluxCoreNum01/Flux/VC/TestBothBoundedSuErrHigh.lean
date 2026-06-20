import ExternSpecs.FluxCoreNum01.Flux.Prelude
import ExternSpecs.FluxCoreNum01.Flux.Fun.NumImpl6MIN
import ExternSpecs.FluxCoreNum01.Flux.Fun.NumImpl6MAX
open Classical
set_option linter.unusedVariables false


namespace F



def TestBothBoundedSuErrHigh := 
 ∀ (x₀ : Int),
  (x₀ > 255) ->
   ((¬((num_impl_6_MIN ≤ x₀) ∧ (x₀ ≤ num_impl_6_MAX))) = True)
end F
