import ExternSpecs.FluxCoreNum01.Flux.Prelude
import ExternSpecs.FluxCoreNum01.Flux.Fun.NumImpl3MAX
open Classical
set_option linter.unusedVariables false


namespace F



def TestUpperBoundedUsErr := 
 ∀ (x₀ : Int),
  (x₀ ≥ 0) ->
   ∀ (a'₁ : Int),
    (a'₁ ≥ 0) ->
     (True -> (a'₁ = 9223372036854775807)) ->
      (x₀ > a'₁) ->
       ((¬(x₀ ≤ num_impl_3_MAX)) = True)
end F
