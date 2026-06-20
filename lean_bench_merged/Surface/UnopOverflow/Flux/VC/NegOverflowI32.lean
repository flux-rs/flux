import Surface.UnopOverflow.Flux.Prelude
import Surface.UnopOverflow.Flux.Fun.NumImpl2MIN
open Classical
set_option linter.unusedVariables false


namespace F



def NegOverflowI32 := 
 ∀ (a₀ : Int),
  (a₀ ≠ num_impl_2_MIN) ->
   (a₀ ≥ (-2147483648)) ->
    (a₀ ≤ 2147483647) ->
     (a₀ ≠ (-2147483648))
end F
