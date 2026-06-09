import LeanProofs.Flux.Prelude
import LeanProofs.Flux.Fun.NumImpl8MAX
open Classical
set_option linter.unusedVariables false


namespace F



def TestIntoUpperBoundedOk := 
 ∀ (x₀ : Int),
  (x₀ ≥ 0) ->
   (x₀ ≤ 4294967295) ->
    ∀ (r₀ : Prop),
     (r₀ = (x₀ ≤ num_impl_8_MAX)) ->
      (r₀ = True)
end F
