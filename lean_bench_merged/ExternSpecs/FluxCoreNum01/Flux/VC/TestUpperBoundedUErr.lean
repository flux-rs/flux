import ExternSpecs.FluxCoreNum01.Flux.Prelude
import ExternSpecs.FluxCoreNum01.Flux.Fun.NumImpl8MAX
open Classical
set_option linter.unusedVariables false


namespace F



def TestUpperBoundedUErr := 
 ∀ (x₀ : Int),
  (x₀ ≥ 0) ->
   (x₀ > 4294967295) ->
    ((¬(x₀ ≤ num_impl_8_MAX)) = True)
end F
